{-# LANGUAGE OverloadedStrings #-}

-- Bytecode remains opt-in while its first-order clause path is established.
-- Compare ordered observations against both existing engines, including the
-- generic driver used when the compiler rejects a clause.
module MachineBytecodeTest (machineBytecodeGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.Char (isSpace)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP (Store (..), emptyStore)
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program (Program)
import Infera.Syntax
import Infera.Unify (canonicalize, emptySubst)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText source = annotate source >> evalEither (parseQuery source)

-- Derived Term equality cannot observe NaN payloads or signed zero. Replace
-- floats only in test observations, after alias-preserving canonicalization.
scalarBits :: Term -> Term
scalarBits (FloatLit number) = Compound "$bytecode_float_bits"
  [IntLit (fromIntegral (castDoubleToWord64 number))]
scalarBits (Compound name arguments) = Compound name (map scalarBits arguments)
scalarBits other = other

canonical :: Query -> [Term] -> [Term]
canonical query terms = case fst (canonicalize emptySubst combined) of
  Compound _ roots -> map scalarBits (drop (length names) roots)
  _ -> error "compound canonicalization changed shape"
  where
    names = map (Var . snd) (queryNames query)
    combined = Compound "$bytecode_observations" (names ++ terms)

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

type TableMetadata = Map.Map Term
  (Bool, Bool, [(Term, Int, [Reference.OutputEvent])], Set.Set Term)

tableMetadata :: Reference.SolverState -> TableMetadata
tableMetadata = Map.mapKeys scalarBits . Map.map entry . Reference.ssTables
  where
    entry table = (Reference.teComplete table, Reference.teTruncated table,
      [(scalarBits term, count, output) | (term, count, output) <- Reference.teAnswers table],
      Set.map scalarBits (Reference.teSet table))

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent] TableMetadata
      (Map.Map PredKey [(Term, Int)])
  | Error SolveError | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
            dynamic = Map.map (map (\(term, count) -> (scalarBits term, count))) (Reference.ssDynamic state)
         in Answer (zip (map fst bindings) (canonical query (map snd bindings)))
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
              (tableMetadata state) dynamic
      Reference.BranchError problem -> Error (normalizeError query problem)
      Reference.BranchExhausted -> Exhausted
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete (scalarBits (fst (canonicalize emptySubst key)))

drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Metrics)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], Machine.checkpointMetrics checkpoint)
    Machine.Yield item next -> do
      (remaining, metrics) <- drain next
      pure (item : remaining, metrics)

compareQuery :: Program -> Query -> PropertyT IO Reference.Search
compareQuery program query = do
  let bytecode = Machine.solveQueryWithBackend Machine.Bytecode program query
      interpreted = Machine.solveQueryWithBackend Machine.Interpreted program query
      reference = Reference.solveQuery program query
  observe query bytecode === observe query interpreted
  observe query bytecode === observe query reference
  observe query (Machine.solveQuery program query) === observe query interpreted
  pure bytecode

compareText :: Program -> String -> PropertyT IO Reference.Search
compareText program source = queryText source >>= compareQuery program

compareMetadata :: Reference.Search -> Reference.Search -> PropertyT IO ()
compareMetadata actual expected = do
  let actualStates = [state | Reference.Found state <- actual]
      expectedStates = [state | Reference.Found state <- expected]
  length actualStates === length expectedStates
  forM_ (zip actualStates expectedStates) $ \(found, original) -> do
    (Reference.ssStore found) {stSubst = emptySubst} ===
      (Reference.ssStore original) {stSubst = emptySubst}
    Reference.ssFresh found === Reference.ssFresh original
    Reference.ssOutLen found === Reference.ssOutLen original
    Reference.ssOutput found === Reference.ssOutput original
    tableMetadata found === tableMetadata original
    Reference.ssDynamic found === Reference.ssDynamic original

prop_generated_ordered_first_order_answers :: Property
prop_generated_ordered_first_order_answers = withTests 200 . property $ do
  numbers <- forAll (Gen.list (Range.linear 0 10) (Gen.integral (Range.linear (-3) 3)))
  let source = unlines
        (["<- notable.", "pick _ <- fail.", "shared X (pair X X).",
          "run Result <- pick X, shared X Result."] ++
         ["pick " ++ show number ++ "." | number <- numbers])
  program <- load source
  query <- queryText "run Result?"
  actual <- compareQuery program query
  [term | Reference.Found state <- actual,
    Just term <- [lookup "Result" (Reference.answerBindings (Reference.projectAnswer query state))]] ===
      [Compound "pair" [IntLit number, IntLit number] | number <- numbers]

prop_generated_head_sharing_and_body_variables :: Property
prop_generated_head_sharing_and_body_variables = withTests 200 . property $ do
  numbers <- forAll (Gen.list (Range.linear 0 7) (Gen.integral (Range.linear (-5) 5)))
  shared <- forAll Gen.bool
  program <- load $ unlines
    [ "<- notable.", "copy X X.", "swap (pair X Y) (pair Y X).",
      "chain Input Result <- swap Input Mid, copy Mid Result.",
      "append [] Ys Ys.", "append [X | Xs] Ys [X | Rest] <- append Xs Ys Rest."
    ]
  let value = mkList (map IntLit numbers) Nothing
      right = if shared then Var 0 else Var 1
      query = Query
        [Compound "chain" [Compound "pair" [value, right], Var 2],
         Compound "copy" [Var 2, Var 3]]
        [("A", 0), ("B", 1), ("Result", 2), ("Again", 3)] 4
  actual <- compareQuery program query
  case [Reference.projectAnswer query state | Reference.Found state <- actual] of
    [answer] -> do
      lookup "Result" (Reference.answerBindings answer) === Just (Compound "pair" [right, value])
      lookup "Again" (Reference.answerBindings answer) === lookup "Result" (Reference.answerBindings answer)
    other -> annotateShow other >> failure

prop_compiled_path_and_direct_call_counters :: Property
prop_compiled_path_and_direct_call_counters = unit $ do
  program <- load "<- notable.\nroot Result <- middle Result.\nmiddle Result <- leaf Result.\nleaf answer."
  query <- queryText "root Result?"
  compiled <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  interpreted <- evalEither (Machine.startMeasuredWithBackend Machine.Interpreted program query)
  (actual, metrics) <- evalEither (drain compiled)
  (expected, oldMetrics) <- evalEither (drain interpreted)
  observe query actual === observe query expected
  observe query actual === observe query (Reference.solveQuery program query)
  assert (Machine.metricCompiledActivations metrics > 0)
  assert (Machine.metricBytecodeInstructions metrics > 0)
  assert (Machine.metricDirectCalls metrics > 0)
  Machine.metricCompiledActivations oldMetrics === 0
  Machine.metricBytecodeInstructions oldMetrics === 0
  Machine.metricDirectCalls oldMetrics === 0
  unmeasured <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  (_, disabled) <- evalEither (drain unmeasured)
  Machine.metricCompiledActivations disabled === 0
  Machine.metricBytecodeInstructions disabled === 0
  Machine.metricDirectCalls disabled === 0

prop_structured_head_tail_collection_and_register_counts :: Property
prop_structured_head_tail_collection_and_register_counts = unit $ do
  program <- load $ unlines
    [ "<- notable.",
      "shape (node (pair X X) [X, X, X] (tag X X X)) X.",
      "down 0 Acc Acc.",
      "down N Acc R <- N > 0, shape (node (pair N N) [N, N, N] (tag N N N)) Value, Next is Acc + Value, M is N - 1, down M Next R."
    ]
  query <- queryText "down 10000 0 Result?"
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, metrics) <- evalEither (drain initial)
  observe query actual === observe query (Reference.solveQuery program query)
  observe query actual === observe query (Machine.solveQueryWithBackend Machine.Interpreted program query)
  case [Reference.projectAnswer query state | Reference.Found state <- actual] of
    [answer] -> Reference.answerBindings answer === [("Result", IntLit 50005000)]
    other -> annotateShow other >> failure
  assert (Machine.metricHeadInstructions metrics > 10000)
  assert (Machine.metricHeadCellsAvoided metrics > 10000)
  assert (Machine.metricMaxActivationRegisters metrics > 0)
  assert (Machine.metricMaxHeapCells metrics <= 4096)
  assert (Machine.metricMaxTasks metrics <= 8)
  assert (Machine.metricCollections metrics > 0)
  assert (Machine.metricTailCalls metrics >= 9000)

prop_contracts_errors_and_small_fuel :: Property
prop_contracts_errors_and_small_fuel = unit $ do
  program <- load $ unlines
    [ "<- notable.", "pick 1.", "pick 2.",
      "bad X <- X is bad.", "bad 3.",
      "out : nondet (int: =>).", "out _.", "out 2.",
      "input : nondet (int: <=).", "input 1.",
      "required : det (atom: =>).", "required _ <- fail.",
      "wrong : nondet (int: =>).", "wrong bad.", "wrong 4.",
      "parent X <- middle X.", "middle X <- pick X."
    ]
  forM_ ["bad X?", "out X?", "input X?", "input bad?", "required X?", "wrong X?", "parent X?"] $ \text -> do
    query <- queryText text
    _ <- compareQuery program query
    forM_ [0, 1, 2, 3, 5] $ \fuel -> do
      annotateShow fuel
      let environment = Reference.mkEnv program
          state = Reference.initialState (queryNVars query)
          expected = Reference.solveGoals environment fuel state (queryGoals query)
      forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
        initial <- evalEither (Machine.startGoalsWithBackend backend environment fuel state (queryGoals query))
        (actual, _) <- evalEither (drain initial)
        observe query actual === observe query expected

prop_generic_control_and_meta_fallback :: Property
prop_generic_control_and_meta_fallback = unit $ do
  program <- load $ unlines
    [ "<- notable.", "pick a.", "pick b.",
      "forward : nondet unsafe (any: <=>).", "forward Goal <- Goal.",
      "local : nondet unsafe (any: <=>).", "local X <- pick X, !.", "local fallback.",
      "conditional X <- (pick X -> true ; X = none).",
      "collect List <- findall X (pick X) List.",
      "effect : unsafe.", "effect X <- (write discarded, fail ; pick X, write X)."
    ]
  forM_
    [ "forward (pick X)?", "forward (once (pick X))?", "local X?",
      "(call (local X, fail) ; X = outer)?", "conditional X?", "collect List?",
      "not (pick absent), pick X?", "findall X (once (pick X)) List?",
      "(pick X, X = b -> pick Y ; Y = none)?", "effect X?",
      "G = (H ; X = otherwise), H = (true -> X = then), forward G?",
      "forward (findall X (pick X) List)?"
    ] $ \text -> compareText program text >> pure ()

prop_stdlib_first_order_execution :: Property
prop_stdlib_first_order_execution = unit $ do
  source <- evalIO (readFile "examples/stdlib.nprolog")
  let definitions = unlines [line | line <- lines source, case dropWhile isSpace line of
        '>' : _ -> False
        _ -> True]
  program <- load ("<- notable.\n" ++ definitions)
  forM_
    [ "append Left Right [1,2,3]?", "reverse [1,2,3,4] Result?",
      "length [a,b,c] N?", "nth [a,b,c] 1 X?", "last [a,b,c] X?",
      "between 1 4 X?", "numlist 1 4 List?", "gcd 84 30 G?",
      "isort [3,1,2,1] Sorted?", "msort [3,1,2] Sorted?",
      "permutation [1,2,3] Result?"
    ] $ \text -> compareText program text >> pure ()

prop_clp_tables_dynamic_and_complete_metadata :: Property
prop_clp_tables_dynamic_and_complete_metadata = unit $ do
  program <- load $ unlines
    [ "<- notable.", "step X Y <- Y #= X + 1.",
      "pick : table nondet (int: <=>).", "pick X <- X #> 1.", "pick 1.",
      "path : table.", "path X Y <- path X Z, edge Z Y.",
      "path X Y <- edge X Y.", "edge a b.", "edge b c.",
      "memo : dynamic.", "effect : unsafe.",
      "effect X <- assert (memo X), memo X."
    ]
  forM_
    [ "[X,Y] in 1..3, step X Y, label [X,Y]?",
      "X in 1..3, pick X, label [X]?", "path a Y, path a Again?",
      "[X,Y] in 1..3, X #< Y, findall (pair X Y) (step X Y, label [X,Y]) List, label [X,Y]?",
      "X in 1..3, once (pick X), label [X]?",
      "assert (memo first), assert (memo second), retract (memo X), memo Y?",
      "(effect discarded, fail ; effect kept)?",
      "path a Before, assert (memo kept), X in 1..3, pick X, label [X], memo Saved?"
    ] $ \text -> do
      query <- queryText text
      actual <- compareQuery program query
      compareMetadata actual (Machine.solveQueryWithBackend Machine.Interpreted program query)
      compareMetadata actual (Reference.solveQuery program query)

prop_retained_interleaved_bytecode_checkpoints :: Property
prop_retained_interleaved_bytecode_checkpoints = unit $ do
  program <- load "<- notable.\npick first.\npick second.\npick third.\nwrap X (pair X X).\nroot R <- pick X, wrap X R."
  query <- queryText "root Result?"
  compiled <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  interpreted <- evalEither (Machine.startWithBackend Machine.Interpreted program query)
  compiledStep <- evalEither (Machine.resume compiled)
  interpretedStep <- evalEither (Machine.resume interpreted)
  case (compiledStep, interpretedStep) of
    (Machine.Yield retained nextCompiled, Machine.Yield oldRetained nextInterpreted) -> do
      let before = observe query [retained]
      _ <- evalIO (evaluate (length (show before)))
      (oldRest, _) <- evalEither (drain nextInterpreted)
      (rest, _) <- evalEither (drain nextCompiled)
      (repeatedRest, _) <- evalEither (drain nextCompiled)
      (again, _) <- evalEither (drain compiled)
      observe query rest === observe query oldRest
      observe query rest === observe query repeatedRest
      before === observe query [retained]
      before === observe query [oldRetained]
      before ++ observe query rest === observe query again
      observe query again === observe query (Reference.solveQuery program query)
    _ -> failure

drainTraced :: Machine.Checkpoint -> Either Heap.HeapError ([Trace.TraceEvent], Reference.Search)
drainTraced checkpoint = do
  (events, step) <- Machine.resumeTraced checkpoint
  case step of
    Machine.Finished -> pure (events, [])
    Machine.Yield item next -> do
      (remainingEvents, remaining) <- drainTraced next
      pure (events ++ remainingEvents, item : remaining)

prop_tracing_retains_source_events_and_prefixes :: Property
prop_tracing_retains_source_events_and_prefixes = unit $ do
  program <- load $ unlines
    [ "<- notable.", "outer X <- inner X.", "inner a.", "inner b.",
      "bad <-", "  X is 1 / 0.", "scope List <- findall X (outer X) List."
    ]
  forM_ ["outer X?", "bad?", "scope List?", "once (outer X)?"] $ \text -> do
    query <- queryText text
    compiled <- evalEither (Machine.startTracedWithBackend Machine.Bytecode program query)
    interpreted <- evalEither (Machine.startTracedWithBackend Machine.Interpreted program query)
    (events, actual) <- evalEither (drainTraced compiled)
    (oldEvents, expected) <- evalEither (drainTraced interpreted)
    events === oldEvents
    assert (not (null events))
    observe query actual === observe query expected
    observe query actual === observe query (Reference.solveQuery program query)
    (repeatedEvents, repeated) <- evalEither (drainTraced compiled)
    repeatedEvents === events
    observe query repeated === observe query actual

prop_nan_signed_zero_and_accepted_startup_aliases :: Property
prop_nan_signed_zero_and_accepted_startup_aliases = unit $ do
  program <- load "<- notable.\ncopy X X.\nchain X Out <- copy X Mid, copy Mid Out."
  let nan = castWord64ToDouble 0x7ff8000000000042
      scalars = [FloatLit nan, FloatLit (-0.0), FloatLit 0.0]
  forM_ scalars $ \scalar -> do
    let query = Query [Compound "chain" [Compound "pair" [scalar, Var 0], Var 1]]
          [("Shared", 0), ("Result", 1)] 2
    actual <- compareQuery program query
    case [Reference.projectAnswer query state | Reference.Found state <- actual] of
      [answer] -> do
        (scalarBits <$> lookup "Result" (Reference.answerBindings answer)) ===
          Just (Compound "pair" [scalarBits scalar, Var 0])
        lookup "Shared" (Reference.answerBindings answer) === Nothing
      other -> annotateShow other >> failure
    let self = query {queryGoals = queryGoals query ++ [Compound "unify" [Var 1, Var 1]]}
    selfItems <- compareQuery program self
    if isNaNScalar scalar then observe self selfItems === [] else pure ()
  let state = (Reference.initialState 4)
        {Reference.ssStore = emptyStore {stSubst = IM.fromList [(0, Var 1), (2, FloatLit nan)]}}
      goals = [Compound "chain" [Compound "pair" [Var 0, Var 2], Var 3]]
      query = Query goals [("A", 0), ("B", 1), ("NaN", 2), ("Out", 3)] 4
      environment = Reference.mkEnv program
      expected = Reference.solveGoals environment 20 state goals
  forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
    initial <- evalEither (Machine.startGoalsWithBackend backend environment 20 state goals)
    (actual, _) <- evalEither (drain initial)
    observe query actual === observe query expected
  where
    isNaNScalar (FloatLit number) = isNaN number
    isNaNScalar _ = False

machineBytecodeGroup :: Group
machineBytecodeGroup = Group "opt-in bytecode driver"
  [ ("generated first-order ordered answers versus both engines", prop_generated_ordered_first_order_answers),
    ("generated structured heads and body variable sharing", prop_generated_head_sharing_and_body_variables),
    ("compiled and direct-call counters exclude total fallback", prop_compiled_path_and_direct_call_counters),
    ("structured head tail collection and register counts", prop_structured_head_tail_collection_and_register_counts),
    ("contracts errors and explicit fuel match both engines", prop_contracts_errors_and_small_fuel),
    ("generic control and meta fallback preserve observations", prop_generic_control_and_meta_fallback),
    ("standard library executes through opt-in bytecode", prop_stdlib_first_order_execution),
    ("CLP tables dynamic facts and complete branch metadata", prop_clp_tables_dynamic_and_complete_metadata),
    ("retained bytecode checkpoints interleave independently", prop_retained_interleaved_bytecode_checkpoints),
    ("traced source events and replay remain unchanged", prop_tracing_retains_source_events_and_prefixes),
    ("NaN bits signed zero and accepted startup aliases", prop_nan_signed_zero_and_accepted_startup_aliases)
  ]
