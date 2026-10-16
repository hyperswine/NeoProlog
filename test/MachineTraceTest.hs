{-# LANGUAGE OverloadedStrings #-}

module MachineTraceTest (machineTraceGroup) where

import Control.Exception (bracket, evaluate)
import Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Trace as Trace
import qualified Infera.Module as Module
import Infera.Program
import Infera.Syntax
import System.Directory (canonicalizePath, getTemporaryDirectory, removeFile)
import System.IO (hClose, hPutStr, openTempFile)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

data Result = Answer String [Reference.OutputEvent] | Error SolveError | Exhausted | Marker Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Result]
observe query = map result
  where
    result (Reference.Found state) = let answer = Reference.projectAnswer query state
      in Answer (Reference.showAnswer answer) (Reference.answerOutput answer)
    result (Reference.BranchError err) = Error err
    result Reference.BranchExhausted = Exhausted
    result (Reference.CutMarker owner) = Marker owner
    result (Reference.ConsumedIncomplete key) = Incomplete key

events :: [Trace.TraceItem] -> [Trace.TraceEvent]
events stream = [event | Trace.TraceEventItem event <- stream]

load :: String -> PropertyT IO Program
load text = annotate text >> evalEither (Reference.loadProgramText text)

queryText :: String -> PropertyT IO Query
queryText text = annotate text >> evalEither (parseQuery text)

prop_source_ordinals_and_utf16 :: Property
prop_source_ordinals_and_utf16 = unit $ do
  located <- evalEither (parseLocatedFile "source.infera" (unlines
    [ "same a.", "other.", "same a.", "bad <- \"😀\" = \"😀\", missing.",
      "arithmetic <-", "  X is 1 / 0."
    ]))
  let sources = Trace.sourceMap located
  first <- evalMaybe (Trace.lookupClauseSource sources ("same", 1) 0)
  second <- evalMaybe (Trace.lookupClauseSource sources ("same", 1) 1)
  spanLine (Trace.sourceClauseSpan first) === 1
  spanLine (Trace.sourceClauseSpan second) === 3
  bad <- evalMaybe (Trace.lookupClauseSource sources ("bad", 0) 0)
  let missing = Trace.goalSourceSpan bad (Atom "missing")
  spanLine missing === 4
  -- Supplementary characters occupy two UTF-16 columns each.
  spanColumn missing === 21
  arithmetic <- evalMaybe (Trace.lookupClauseSource sources ("arithmetic", 0) 0)
  spanLine (Trace.goalSourceSpan arithmetic
    (Compound "is" [Var 0, Compound "div" [IntLit 1, IntLit 0]])) === 6

prop_append_and_ambiguous_sites :: Property
prop_append_and_ambiguous_sites = unit $ do
  first <- evalEither (parseLocatedFile "first.infera" "p <- q, q.")
  second <- evalEither (parseLocatedFile "second.infera" "p <- r.")
  let sources = Trace.appendSourceMap (Trace.sourceMap first) second
  p0 <- evalMaybe (Trace.lookupClauseSource sources ("p", 0) 0)
  p1 <- evalMaybe (Trace.lookupClauseSource sources ("p", 0) 1)
  Trace.goalSourceSpan p0 (Atom "q") === Trace.sourceClauseSpan p0
  spanFile (Trace.goalSourceSpan p1 (Atom "r")) === "second.infera"

prop_generated_trace_preserves_stream :: Property
prop_generated_trace_preserves_stream = withTests 200 . property $ do
  count <- forAll (Gen.int (Range.linear 0 8))
  context <- forAll (Gen.element
    [ "pick X?", "once (pick X)?", "not (pick impossible)?",
      "findall X (pick X) L?", "(pick X -> true ; X = absent)?",
      "(pick X, fail ; X = fallback)?", "X in 0..2, label [X]?",
      "bad?", "outer X?"
    ])
  program <- load (unlines
    (["<- notable.", "bad <- X is 1 / 0.", "outer X <- pick X."]
      ++ ["pick " ++ show index ++ "." | index <- [0 .. count]]))
  query <- queryText context
  let traced = Trace.traceQuery program query
  observe query (Trace.traceSearch traced) === observe query (Reference.solveQuery program query)
  observe query (Trace.traceSearch traced) === observe query (Machine.solveQuery program query)

prop_ports_and_frames :: Property
prop_ports_and_frames = unit $ do
  program <- load (unlines
    [ "<- notable.", "parent X <- choice X.", "choice a.", "choice b.",
      "committed : unsafe.", "committed X <- choice X, !."
    ])
  query <- queryText "parent X?"
  let emitted = events (Trace.traceQuery program query)
      ports = map Trace.tracePort emitted
      nested = [event | event <- emitted, functorOf (Trace.traceGoal event) == Just ("choice", 1)]
  forM_ [Trace.Call, Trace.Exit, Trace.Redo] $ \port -> assert (port `elem` ports)
  assert (any (elem ("parent", 1) . map Trace.traceFramePredicate . Trace.traceFrames) nested)
  assert (all (not . null . Trace.renderTraceEvent) emitted)
  cutQuery <- queryText "committed X?"
  assert (Trace.Cut `elem` map Trace.tracePort (events (Trace.traceQuery program cutQuery)))
  falseQuery <- queryText "false?"
  assert (Trace.Fail `elem` map Trace.tracePort (events (Trace.traceQuery program falseQuery)))
  forM_
    [ "((choose X, !) -> choose Y ; X = otherwise)?",
      "(call (choose X, !, fail) ; X = fallback)?",
      "once (call (choose X, !)), choose Y?",
      "findall X (choose X, !) L, choose Y?"
    ] $ \text -> do
      nestedQuery <- queryText text
      observe nestedQuery (Trace.traceSearch (Trace.traceQuery program nestedQuery))
        === observe nestedQuery (Reference.solveQuery program nestedQuery)
  -- A caller-owned marker travels through an unsafe variable invocation. A
  -- later local cut suppresses it before fresh condition/call choices appear.
  foreignProgram <- load (unlines
    [ "<- notable.", "run : nondet unsafe (any: <=>) (any: <=>).",
      "forward : nondet unsafe (any: <=>).", "forward G <- G.",
      "choose a.", "choose b.",
      "run G first <- forward G, !, (true -> choose _ ; fail), !.",
      "run _ second."
    ])
  let callerQuery = Query
        [Compound ";" [Compound "run" [Atom "!", Var 0], Compound "unify" [Var 0, Atom "otherwise"]]]
        [("X", 0)] 1
  observe callerQuery (Trace.traceSearch (Trace.traceQuery foreignProgram callerQuery))
    === observe callerQuery (Reference.solveQuery foreignProgram callerQuery)

prop_located_runtime_error :: Property
prop_located_runtime_error = unit $ do
  program <- load (unlines ["<- notable.", "outer <- inner.", "inner <-", "  X is 1 / 0."])
  query <- queryText "outer?"
  let traced = Trace.traceQuery program query
      errors = [event | event <- events traced, Trace.traceError event == Just DivisionByZero]
  event <- evalMaybe (case errors of value : _ -> Just value; [] -> Nothing)
  site <- evalMaybe (Trace.traceSpan event)
  spanFile site === "<program>"
  spanLine site === 4
  assert (("inner", 0) `elem` map Trace.traceFramePredicate (Trace.traceFrames event))
  assert (("outer", 0) `elem` map Trace.traceFramePredicate (Trace.traceFrames event))
  observe query (Trace.traceSearch traced) === [Error DivisionByZero]
  declared <- load (unlines ["p : semidet (int: =>).", "p X <- true."])
  declaredQuery <- queryText "p X?"
  let contractErrors = [event' | event' <- events (Trace.traceQuery declared declaredQuery),
        case Trace.traceError event' of Just (OutputModeError _ _ _) -> True; _ -> False]
  contract <- evalMaybe (case contractErrors of value : _ -> Just value; [] -> Nothing)
  functorOf (Trace.traceGoal contract) === Just ("p", 1)
  declaredSite <- evalMaybe (Trace.traceSpan contract)
  spanLine declaredSite === 2
  assert (("p", 1) `elem` map Trace.traceFramePredicate (Trace.traceFrames contract))
  tabled <- load (unlines
    ["<- notable.", "p : table.", "p <- helper.", "helper <-", "  X is 1 / 0."])
  tabledQuery <- queryText "p?"
  let tabledTrace = Trace.traceQuery tabled tabledQuery
      tabledErrors = [event' | event' <- events tabledTrace,
        Trace.traceError event' == Just DivisionByZero,
        any ((== ("helper", 0)) . Trace.traceFramePredicate) (Trace.traceFrames event')]
  tabledError <- evalMaybe (case tabledErrors of value : _ -> Just value; [] -> Nothing)
  tabledSite <- evalMaybe (Trace.traceSpan tabledError)
  spanFile tabledSite === "<program>"
  spanLine tabledSite === 5
  assert (("p", 0) `elem` map Trace.traceFramePredicate (Trace.traceFrames tabledError))
  observe tabledQuery (Trace.traceSearch tabledTrace) === observe tabledQuery (Reference.solveQuery tabled tabledQuery)
  constrained <- load (unlines
    ["p : table.", "p bad.", "outer X <- X in 1..3, p X."])
  constrainedQuery <- queryText "outer X?"
  let constrainedTrace = Trace.traceQuery constrained constrainedQuery
      headErrors = [event' | event' <- events constrainedTrace,
        case Trace.traceError event' of Just (CLPTypeError _) -> True; _ -> False]
  headError <- evalMaybe (case headErrors of value : _ -> Just value; [] -> Nothing)
  headSite <- evalMaybe (Trace.traceSpan headError)
  spanLine headSite === 2
  map Trace.traceFramePredicate (Trace.traceFrames headError) === [("p", 1), ("outer", 1)]
  observe constrainedQuery (Trace.traceSearch constrainedTrace)
    === observe constrainedQuery (Reference.solveQuery constrained constrainedQuery)

prop_expanded_dcg_and_source_loader :: Property
prop_expanded_dcg_and_source_loader = unit $ do
  loaded <- evalIO (Module.loadSource Map.empty (unlines ["<- notable.", "bad -> { X is 1 / 0 }."]))
  (program, _) <- evalEither loaded
  query <- queryText "phrase bad nil?"
  let emitted = events (Trace.traceQuery program query)
      errors = [event | event <- emitted, Trace.traceError event == Just DivisionByZero]
  event <- evalMaybe (case errors of value : _ -> Just value; [] -> Nothing)
  site <- evalMaybe (Trace.traceSpan event)
  spanFile site === "<source>"
  spanLine site === 2

prop_imported_runtime_origin :: Property
prop_imported_runtime_origin = unit $ do
  temporary <- evalIO getTemporaryDirectory
  (path, loaded) <- evalIO $ bracket (openTempFile temporary "infera-trace-import.infera")
    (\(file, _) -> removeFile file) $ \(file, handle) -> do
      hPutStr handle "inner <-\n  X is 1 / 0.\n> inner?\n"
      hClose handle
      canonical <- canonicalizePath file
      result <- Module.loadSource (Map.singleton "dep#trace" file)
        "<- import \"dep#trace\".\nouter <- dep:inner.\n"
      pure (canonical, result)
  (program, inline) <- evalEither loaded
  length inline === 0
  query <- queryText "outer?"
  let errors = [event | event <- events (Trace.traceQuery program query),
        Trace.traceError event == Just DivisionByZero]
  event <- evalMaybe (case errors of value : _ -> Just value; [] -> Nothing)
  site <- evalMaybe (Trace.traceSpan event)
  spanFile site === path
  spanLine site === 2
  assert (("dep:inner", 0) `elem` map Trace.traceFramePredicate (Trace.traceFrames event))

prop_trace_checkpoint_independence :: Property
prop_trace_checkpoint_independence = unit $ do
  program <- load (unlines ["<- notable.", "p a.", "p b."])
  query <- queryText "p X?"
  initial <- evalEither (Machine.startTraced program query)
  (firstEvents, firstStep) <- evalEither (Machine.resumeTraced initial)
  next <- case firstStep of
    Machine.Yield (Reference.Found _) checkpoint -> pure checkpoint
    _ -> failure
  (secondEvents, _) <- evalEither (Machine.resumeTraced next)
  _ <- evalIO (evaluate (length (show secondEvents)))
  (repeatedEvents, repeatedStep) <- evalEither (Machine.resumeTraced initial)
  repeatedEvents === firstEvents
  case (firstStep, repeatedStep) of
    (Machine.Yield item _, Machine.Yield repeated _) -> observe query [repeated] === observe query [item]
    _ -> failure
  mutual <- load (unlines
    ["<- notable.", "left : table.", "right : table.",
      "left a.", "left X <- right X.", "right X <- left X."])
  mutualQuery <- queryText "left X?"
  let mutualTrace = Trace.traceQuery mutual mutualQuery
  observe mutualQuery (Trace.traceSearch mutualTrace) === observe mutualQuery (Reference.solveQuery mutual mutualQuery)
  assert (any ((== Just ("right", 1)) . functorOf . Trace.traceGoal) (events mutualTrace))

machineTraceGroup :: Group
machineTraceGroup = Group "machine tracing and runtime source locations"
  [ ("stable clause ordinals and UTF-16 operator sites", prop_source_ordinals_and_utf16),
    ("interactive metadata and ambiguous source sites", prop_append_and_ambiguous_sites),
    ("generated traced and ordinary ordered streams", prop_generated_trace_preserves_stream),
    ("call exit redo ports and activation chains", prop_ports_and_frames),
    ("located runtime errors preserve public error kinds", prop_located_runtime_error),
    ("expanded DCG and source loader retain origins", prop_expanded_dcg_and_source_loader),
    ("qualified imports retain runtime source identities", prop_imported_runtime_origin),
    ("traced checkpoints remain immutable and repeatable", prop_trace_checkpoint_independence)
  ]
