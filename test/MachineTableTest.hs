{-# LANGUAGE OverloadedStrings #-}

-- Native variant tables retain the reference's ordered observations, not
-- only their answer sets. Graph closure supplies an independent answer oracle.
module MachineTableTest (machineTableGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (sort)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP (Store (..))
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import qualified Infera.Machine.Table as Table
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program
import Infera.Syntax
import Infera.Unify (canonicalize, emptySubst)

type TableMetadata = Map.Map Term
  (Bool, Bool, [(Term, Int, [Reference.OutputEvent])], Set.Set Term)

tableMetadata :: Reference.SolverState -> TableMetadata
tableMetadata = Map.map entry . Reference.ssTables
  where
    entry table = (Reference.teComplete table, Reference.teTruncated table,
      Reference.teAnswers table, Reference.teSet table)

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent] TableMetadata (Map.Map PredKey [(Term, Int)])
  | Exhausted
  | Error SolveError
  | Cut Int
  | Incomplete Term
  deriving (Eq, Show)

canonical :: Query -> [Term] -> [Term]
canonical query terms = case fst (canonicalize emptySubst combined) of
  Compound _ roots -> drop (length names) roots
  _ -> error "compound canonicalization changed shape"
  where
    names = map (Var . snd) (queryNames query)
    combined = Compound "$observations" (names ++ terms)

normalizeError :: Query -> SolveError -> SolveError
normalizeError query problem = case problem of
  InstantiationError term -> InstantiationError (term' term)
  ExpectedInteger term -> ExpectedInteger (term' term)
  ExpectedNumber term -> ExpectedNumber (term' term)
  ModeError key index term -> ModeError key index (term' term)
  OutputModeError key index term -> OutputModeError key index (term' term)
  SortError key index sort' term -> SortError key index sort' (term' term)
  CLPTypeError term -> CLPTypeError (term' term)
  UnboundedDomain term -> UnboundedDomain (term' term)
  TypeError description term -> TypeError description (term' term)
  other -> other
  where
    term' term = case canonical query [term] of
      [value] -> value
      _ -> error "canonicalization changed root count"

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
         in Answer (zip (map fst bindings) (canonical query (map snd bindings)))
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
              (tableMetadata state) (Reference.ssDynamic state)
      Reference.BranchExhausted -> Exhausted
      Reference.BranchError problem -> Error (normalizeError query problem)
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete (fst (canonicalize emptySubst key))

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText text = annotate text >> evalEither (parseQuery text)

compareQuery :: Program -> Query -> PropertyT IO Reference.Search
compareQuery program query = do
  let actual = Machine.solveQuery program query
  observe query actual === observe query (Reference.solveQuery program query)
  pure actual

compareText :: String -> String -> PropertyT IO Reference.Search
compareText source text = load source >>= \program -> queryText text >>= compareQuery program

node :: Int -> String
node value = "n" ++ show value

closure :: [(Int, Int)] -> Int -> [Term]
closure edges start = map (Atom . node) . Set.toAscList $
  settle (Set.fromList [b | (a, b) <- edges, a == start])
  where
    settle reached =
      let next = Set.union reached (Set.fromList [b | (a, b) <- edges, Set.member a reached])
       in if next == reached then reached else settle next

prop_generated_graph_tables :: Property
prop_generated_graph_tables = withTests 200 . property $ do
  size <- forAll (Gen.int (Range.linear 1 6))
  edges <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  start <- forAll (Gen.int (Range.linear 0 (size - 1)))
  recursiveFirst <- forAll Gen.bool
  duplicateFacts <- forAll Gen.bool
  indexed <- forAll Gen.bool
  let recursive = "path X Y <- path X Z, edge Z Y."
      base = "path X Y <- edge X Y."
      facts = ["edge " ++ node a ++ " " ++ node b ++ "." | (a, b) <- edges]
      source = unlines $
        [if indexed then "<- index." else "<- noindex.", "edge _ _ <- fail."]
        ++ facts ++ [fact | duplicateFacts, fact <- facts]
        ++ if recursiveFirst then [recursive, base] else [base, recursive]
  classify "indexed" indexed
  classify "duplicate edge facts" duplicateFacts
  program <- load source
  query <- queryText ("path " ++ node start ++ " Target?")
  actual <- compareQuery program query
  let summary = Reference.summarizeSearch query actual
      answers = [term | answer <- Reference.summaryAnswers summary,
                        Just term <- [lookup "Target" (Reference.answerBindings answer)]]
  sort answers === sort (closure edges start)
  Reference.summaryErrors summary === []
  Reference.summaryExhausted summary === False

prop_mutual_nonlinear_variants :: Property
prop_mutual_nonlinear_variants = unit $ forM_
  [ ("p X <- q X.\nq X <- p X.\np first.\nq second.", "p Result?"),
    ("path X Y <- path X Z, path Z Y.\npath a b.\npath b c.\npath c a.", "path a Result?"),
    ("path X Y <- edge X Z, path Z Y.\npath X Y <- edge X Y.\nedge a b.\nedge b c.", "path a Result?"),
    ("p X <- p Y, rel Y X.\np a.\nrel a b.\nrel b c.\nrel c a.", "p Result?"),
    ("path X Y <- path X Z, red Z Y.\npath X Y <- red X Y.\npath X Y <- path X Z, blue Z Y.\npath X Y <- blue X Y.\nred a b.\nblue b c.", "path From To?")
  ] $ \(source, text) -> do
    _ <- compareText source text
    pure ()

prop_open_answers_and_cached_aliases :: Property
prop_open_answers_and_cached_aliases = unit $ do
  let source = unlines
        ["p Pair Y <- p Pair Z, step Z Y.", "p (pair a a) first.",
         "p (pair X X) open.", "step first second.", "step open shared.",
         "step second third."]
  forM_
    [ "p (pair X X) Result?", "p (pair X Y) Result?",
      "Pair = pair X Y, X = Y, p Pair Result?",
      "p (pair a X) Result, p (pair a X) Again?",
      "findall (pair X Result) (p (pair X X) Result) Answers?"
    ] $ \text -> do
      _ <- compareText source text
      pure ()

prop_contracts_not_applied_twice :: Property
prop_contracts_not_applied_twice = unit $ forM_
  [ ("p : table semidet (atom: <=>).\np X <- p X.\np first.\np second.", "p Result?"),
    ("p : table det (atom: =>).\np X <- p X.", "p Result?"),
    ("p : table multi (atom: =>).\np X <- p X.\np first.\np second.", "p Result?"),
    ("p : table nondet (int: =>).\np X <- p X.\np bad.", "p Result?"),
    ("p : table nondet (atom: <=).\np X <- p X.\np first.", "p Result?"),
    ("p : table nondet (any: =>).\np X <- p X.\np X.", "p Result?")
  ] $ \(source, text) -> do
    _ <- compareText source text
    pure ()

prop_effect_errors_cuts_and_output :: Property
prop_effect_errors_cuts_and_output = unit $ forM_
  [ ("p X <- p X.\np answer.\np X <- missing X.", "p Result?"),
    ("p : table unsafe.\np X <- p Y, X = Y.\np answer <- write seen.", "p Result?"),
    ("p : table unsafe.\np X <- p Y, !, X = Y.\np first.\np second.", "p Result?"),
    ("p : table unsafe.\np X <- p X.\np a <- write a.\np a <- write duplicate.\np b <- write b.", "p Result?"),
    ("p X <- p X.\np first.\np second.", "p Result, (Result = first -> ! ; true)?"),
    ("p X <- p X.\np first.\np second.", "once (p Result), Result = second?")
  ] $ \(source, text) -> do
    _ <- compareText source text
    pure ()

prop_constrained_inputs_and_answers :: Property
prop_constrained_inputs_and_answers = unit $ forM_
  [ ("p X <- p Y, X #= Y, X in 0..2.\np 1.", "p Result?"),
    ("p : table.\np X <- X in 1..3.", "p Result?"),
    ("p X <- p X.\np 1.\np 2.\np 3.", "Result in 1..2, p Result, label [Result]?"),
    ("p X <- p Y, X #= Y + 1, X in 0..2.\np 0.", "p Result?")
  ] $ \(source, text) -> do
    program <- load source
    query <- queryText text
    -- Constrained table calls intentionally fall back to plain resolution.
    -- Left recursion on that path is a resource-limit fixture, so exercise
    -- small explicit limits instead of forcing the default 100,000 levels.
    forM_ [0, 1, 3, 6] $ \fuel -> do
      annotateShow fuel
      let environment = Reference.mkEnv program
          state = Reference.initialState (queryNVars query)
          actual = Machine.solveGoals environment fuel state (queryGoals query)
          expected = Reference.solveGoals environment fuel state (queryGoals query)
      observe query actual === observe query expected
      let actualStates = [found | Reference.Found found <- actual]
          expectedStates = [found | Reference.Found found <- expected]
      length actualStates === length expectedStates
      forM_ (zip actualStates expectedStates) $ \(found, original) ->
        (Reference.ssStore found) {stSubst = emptySubst} ===
          (Reference.ssStore original) {stSubst = emptySubst}

prop_scopes_restore_tables_and_dynamic_state :: Property
prop_scopes_restore_tables_and_dynamic_state = unit $ do
  let source = "fact : dynamic.\np X <- q X.\nq X <- p X.\nq seed."
  forM_
    [ "call (p X)?", "once (p X)?", "not (p X)?",
      "(p X -> X = seed ; X = otherwise)?", "findall X (call (p X)) List?",
      "not (assert (fact child), p X, write child, fail), fact Y?",
      "findall X (assert (fact child), p X, write child) List, (fact Y ; Y = absent)?",
      "once (assert (fact child), p X, write child), fact Y?",
      "call (assert (fact child), p X, write child), fact Y?",
      "((assert (fact child), p X, write child) -> fact Y ; fail)?",
      "(assert (fact branch), p X, fail ; p X, (fact Y ; Y = absent))?"
    ] $ \text -> do
      _ <- compareText source text
      pure ()

prop_raw_table_callback_and_cache :: Property
prop_raw_table_callback_and_cache = unit $ do
  program <- load "p X <- p Y, step Y X.\np a.\nstep a b.\nstep b c."
  query <- queryText "p Result?"
  predicate <- evalMaybe (lookupPred ("p", 1) program)
  goal <- case queryGoals query of
    [value] -> pure value
    _ -> failure
  let environment = Reference.mkEnv program
      state = Reference.initialState (queryNVars query)
      native = Table.evalTabled Machine.solveGoals environment Reference.maxResolutionDepth state predicate goal
      expected = Reference.solveGoals environment Reference.maxResolutionDepth state [goal]
  observe query native === observe query expected
  -- Cached answers own canonical syntax and output. Consuming them must not
  -- launch a clause body, even with zero resolution fuel.
  let entry = Reference.TableEntry True False
        [(Compound "p" [Compound "pair" [Var 0, Var 0]], 1, [Reference.WriteEvent "cached"])]
        (Set.singleton (Compound "p" [Compound "pair" [Var 0, Var 0]]))
      key = fst (canonicalize emptySubst goal)
      cached = state {Reference.ssTables = Map.singleton key entry}
      forbidden _ _ _ _ = error "cached table unexpectedly invoked native clause evaluation"
      items = Table.evalTabled forbidden environment 0 cached predicate goal
  case items of
    [Reference.Found found] -> do
      Reference.ssFresh found === Reference.ssFresh state + 1
      Reference.ssOutput found === [Reference.WriteEvent "cached"]
      let answer = Reference.projectAnswer query found
      map snd (Reference.answerBindings answer) === [Compound "pair" [Var (queryNVars query), Var (queryNVars query)]]
    _ -> failure

prop_seeded_cache_metadata_at_zero_fuel :: Property
prop_seeded_cache_metadata_at_zero_fuel = unit $ do
  program <- load "p X <- p X.\np first.\np second."
  query <- queryText "p Result?"
  let key = Compound "p" [Var 0]
      answers = [(Compound "p" [Atom "cached"], 0,
                  [Reference.WriteEvent "before", Reference.NewlineEvent, Reference.WriteEvent "after"])]
      answerSet = Set.singleton (Compound "p" [Atom "cached"])
      environment = Reference.mkEnv program
  forM_ [(True, False), (True, True), (False, False)] $ \(complete, truncated) -> do
    annotateShow (complete, truncated)
    let entry = Reference.TableEntry complete truncated answers answerSet
        state = (Reference.initialState (queryNVars query))
          {Reference.ssTables = Map.singleton key entry}
        actual = Machine.solveGoals environment 0 state (queryGoals query)
        expected = Reference.solveGoals environment 0 state (queryGoals query)
    observe query actual === observe query expected
    let found = [result | Reference.Found result <- actual]
    length found === 1
    case found of
      [result] -> Reference.answerOutput (Reference.projectAnswer query result) ===
        [Reference.WriteEvent "before", Reference.NewlineEvent, Reference.WriteEvent "after"]
      _ -> failure

prop_instrumentation_does_not_change_tables :: Property
prop_instrumentation_does_not_change_tables = unit $ do
  forM_
    [ "p X <- p X.\np seed.",
      "p X <- q X.\nq X <- p X.\nq seed.",
      "p X <- p Y, step Y X.\np a.\nstep a b.\nstep b c.",
      "p X <- p X.\np answer.\np X <- missing X.",
      "p : table unsafe.\np X <- p Y, !, X = Y.\np first.\np second.",
      "p : table.\np X <- X in 1..3."
    ] $ \source -> do
      program <- load source
      query <- queryText "p Result?"
      predicate <- evalMaybe (lookupPred ("p", 1) program)
      goal <- case queryGoals query of
        [value] -> pure value
        _ -> failure
      let environment = Reference.mkEnv program
          state = Reference.initialState (queryNVars query)
          callback env fuel current goals frames =
            [Left (Trace.TraceEvent Trace.Call term site frames Nothing) | (term, site) <- goals]
              ++ map Right (Machine.solveGoals env fuel current (map fst goals))
          traced = Table.evalTabledTraced callback environment 20 state predicate goal
          actual = [item | Right item <- traced]
          expected = Table.evalTabled Machine.solveGoals environment 20 state predicate goal
      observe query actual === observe query expected
      assert (not (null [event | Left event <- traced]))
  -- The general table path abandons its remaining producer retries as soon
  -- as it finds a constrained answer and restarts plain evaluation. Looking
  -- for trace events must not force that abandoned suffix before the plain
  -- fallback's first answer becomes available.
  program <- load "p : table.\np X <- X in 1..3.\np X <- poison X."
  query <- queryText "p Result?"
  predicate <- evalMaybe (lookupPred ("p", 1) program)
  goal <- case queryGoals query of
    [value] -> pure value
    _ -> failure
  let callback env fuel current goals frames
        | any ((== Just ("poison", 1)) . functorOf . fst) goals =
            error "tracing forced an abandoned table producer suffix"
        | otherwise =
            [Left (Trace.TraceEvent Trace.Call term site frames Nothing) | (term, site) <- goals]
              ++ map Right (Machine.solveGoals env fuel current (map fst goals))
      state = Reference.initialState (queryNVars query)
      traced = Table.evalTabledTraced callback (Reference.mkEnv program) 20 state predicate goal
      first = take 1 [Reference.Found found | Right (Reference.Found found) <- traced]
      expected = take 1 [Reference.Found found | Reference.Found found <-
        Table.evalTabled Machine.solveGoals (Reference.mkEnv program) 20 state predicate goal]
  observe query first === observe query expected

prop_resolution_and_iteration_exhaustion :: Property
prop_resolution_and_iteration_exhaustion = unit $ do
  program <- load (unlines
    ["p X <- p Y, edge Y X.", "p root.", "p X <- helper X.",
     "edge root next.", "helper X <- deeper X.", "deeper other."])
  query <- queryText "p Result?"
  forM_ [0, 1, 2, 3] $ \fuel -> do
    annotateShow fuel
    let environment = Reference.mkEnv program
        state = Reference.initialState (queryNVars query)
        native = Machine.solveGoals environment fuel state (queryGoals query)
        expected = Reference.solveGoals environment fuel state (queryGoals query)
    observe query native === observe query expected
  limited <- load "p : table.\np (next X) <- p X.\np zero."
  limitedQuery <- queryText "p Result?"
  actual <- compareQuery limited limitedQuery
  let summary = Reference.summarizeSearch limitedQuery actual
  Reference.summaryExhausted summary === True
  length (Reference.summaryAnswers summary) === 301

-- A completed table must remain immutable while the answer iterator advances
-- and while an older checkpoint is resumed independently.
drain :: Machine.Checkpoint -> Either Heap.HeapError Reference.Search
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure []
    Machine.Yield item next -> (item :) <$> drain next

prop_retained_table_checkpoints :: Property
prop_retained_table_checkpoints = unit $ do
  program <- load "p X <- p X.\np first.\np second.\np third."
  query <- queryText "p Result?"
  initial <- evalEither (Machine.start program query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = observe query [retained]
      _ <- evalIO (evaluate (length (show before)))
      rest <- evalEither (drain next)
      repeatRest <- evalEither (drain next)
      repeatAll <- evalEither (drain initial)
      observe query rest === observe query repeatRest
      before === observe query [retained]
      before ++ observe query rest === observe query repeatAll
      observe query repeatAll === observe query (Reference.solveQuery program query)

machineTableGroup :: Group
machineTableGroup = Group "native variant tables"
  [ ("generated ordered graph tables versus reference and closure", prop_generated_graph_tables),
    ("mutual nonlinear and different-variant fixedpoints", prop_mutual_nonlinear_variants),
    ("canonical open answers and cached aliases", prop_open_answers_and_cached_aliases),
    ("table contracts apply once at the native activation", prop_contracts_not_applied_twice),
    ("table effects errors cuts and ordered output", prop_effect_errors_cuts_and_output),
    ("constrained calls and answers retain plain native fallback", prop_constrained_inputs_and_answers),
    ("opaque scopes restore tables and dynamic state", prop_scopes_restore_tables_and_dynamic_state),
    ("standalone native callback and immutable cache consumption", prop_raw_table_callback_and_cache),
    ("complete incomplete and truncated caches at zero fuel", prop_seeded_cache_metadata_at_zero_fuel),
    ("producer instrumentation preserves tables and finite prefixes", prop_instrumentation_does_not_change_tables),
    ("table resolution and iteration exhaustion", prop_resolution_and_iteration_exhaustion),
    ("retained table checkpoints resume independently", prop_retained_table_checkpoints)
  ]
