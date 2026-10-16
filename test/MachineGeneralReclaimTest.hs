{-# LANGUAGE OverloadedStrings #-}

-- Collection traces the active branch independently of its frozen choices
-- and callers. Work may be exponential while live heap state is bounded by
-- continuation depth; output and genuine retained answers may still grow.
module MachineGeneralReclaimTest (machineGeneralReclaimGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP (Store (..))
import qualified Infera.Engine.Reference as Reference
import Infera.Error (SolveError (..))
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program (Program)
import Infera.Syntax
import Infera.Unify (deepWalk, emptySubst)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

source :: String
source = unlines
  [ "<- notable.",
    "fib 0 0.", "fib 1 1.",
    "fib N F <- N > 1, A is N - 1, B is N - 2, fib A FA, fib B FB, F is FA + FB.",
    "outer : unsafe.", "outer N F <- write kept, fib N F, !, true.",
    "cut_after : nondet unsafe (int: <=) (any: <=>).",
    "cut_after N F <- (F = rejected, fail ; fib N F), !.",
    "cut_after _ ignored.",
    "loud : unsafe.", "loud 0 <- write zero.", "loud 1 <- write one.",
    "loud N <- N > 1, A is N - 1, B is N - 2, loud A, loud B, true.",
    "memo : dynamic.", "seed : table.", "seed seeded.",
    "badout : semidet (int: =>).", "badout R <- fib 13 N, R = bad.",
    "missingout : semidet (int: =>).", "missingout R <- fib 13 N.",
    "required : det (int: =>).", "required R <- fib 13 N, fail."
  ]

load :: PropertyT IO Program
load = evalEither (Reference.loadProgramText source)

data Event
  = Answer Reference.Answer
  | Error SolveError | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state -> Answer (Reference.projectAnswer query state)
      Reference.BranchError problem -> Error problem
      Reference.BranchExhausted -> Exhausted
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete key

drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Checkpoint)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> Right ([], checkpoint)
    Machine.Yield item next -> do
      (rest, final) <- drain next
      Right (item : rest, final)

run :: Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
run program query = do
  initial <- evalEither (Machine.startMeasured program query)
  (items, final) <- evalEither (drain initial)
  _ <- evalIO (evaluate (length (show (observe query items))))
  pure (items, Machine.checkpointMetrics final)

compareQuery :: Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
compareQuery program query = do
  result@(items, _) <- run program query
  observe query items === observe query (Reference.solveQuery program query)
  pure result

compareText :: Program -> String -> PropertyT IO (Reference.Search, Machine.Metrics)
compareText program text = do
  annotate text
  query <- evalEither (parseQuery text)
  compareQuery program query

fib :: Int -> Integer
fib count = fst (iterate (\(a, b) -> (b, a + b)) (0, 1) !! count)

prop_generated_scope_cut_constraint_contexts :: Property
prop_generated_scope_cut_constraint_contexts = withTests 100 . property $ do
  program <- load
  count <- forAll (Gen.int (Range.linear 8 12))
  context <- forAll (Gen.element
    [ "fib % F?",
      "once (fib % F)?",
      "not (fib % F, fail), R = done?",
      "(fib % F -> R = then ; R = otherwise)?",
      "(fib % F, fail ; R = fallback)?",
      "findall (pair X F) ((X = one ; X = two), fib % F) Answers?",
      "X in 1..3, X #!= 2, fib % F, label [X]?",
      "outer % F?",
      "cut_after % F?"
    ])
  let replace [] = []
      replace ('%' : rest) = show count ++ replace rest
      replace (character : rest) = character : replace rest
  (_, metrics) <- compareText program (replace context)
  assert (Machine.metricCollections metrics > 0)
  Machine.metricTailCalls metrics === 0

prop_non_tail_exponential_work_has_bounded_active_heap :: Property
prop_non_tail_exponential_work_has_bounded_active_heap = unit $ do
  program <- load
  results <- mapM (\count -> do
    query <- evalEither (parseQuery ("fib " ++ show count ++ " F?"))
    (items, metrics) <- compareQuery program query
    [deepWalk (stSubst (Reference.ssStore state)) (Var 0) | Reference.Found state <- items] === [IntLit (fib count)]
    Machine.metricTailCalls metrics === 0
    assert (Machine.metricCollections metrics > 0)
    assert (Machine.metricMaxTasks metrics <= 8 * count + 32)
    assert (Machine.metricMaxHeapCells metrics <= 16384)
    assert (Machine.metricMaxBindings metrics <= 2048)
    assert (Machine.metricMaxSubstitutions metrics <= 2048)
    pure metrics) [12, 18]
  case results of
    [small, large] -> do
      assert (Machine.metricCalls large > 10 * Machine.metricCalls small)
      assert (Machine.metricMaxHeapCells large <= 3 * Machine.metricMaxHeapCells small + 2048)
    _ -> failure

prop_active_clp_metadata_survives_repeated_collection :: Property
prop_active_clp_metadata_survives_repeated_collection = unit $ do
  program <- load
  forM_
    [ "[X, Y] in 1..4, X #< Y, reify (X #< 3) B, fib 14 F?",
      "[X, Y] in 1..4, X #< Y, reify (X #< 3) B, once (fib 14 F), label [X, Y, B]?"
    ] $ \text -> do
      query <- evalEither (parseQuery text)
      (items, metrics) <- compareQuery program query
      assert (Machine.metricCollections metrics > 0)
      let stores search = [(Reference.ssStore state) {stSubst = emptySubst} | Reference.Found state <- search]
      -- Compare all scheduler/domain/residual fields, not just rendered
      -- constraints. Internal dead substitution entries may be reclaimed.
      stores items === stores (Reference.solveQuery program query)

prop_dynamic_tables_and_freshness_survive_collection :: Property
prop_dynamic_tables_and_freshness_survive_collection = unit $ do
  program <- load
  forM_
    [ "assert (memo (pair A A)), seed S, fib 14 F, memo (pair B C), B = kept, memo (pair D E), D = other, retractall (memo _), not (memo _)?",
      -- This first table invocation occurs only after the outer machine has
      -- reclaimed many activations. Native table-clause startup must retain
      -- referenced logical roots without resurrecting the full ssFresh range.
      "assert (memo (pair A A)), fib 14 F, seed S, memo (pair B C), B = kept, memo (pair D E), D = other, retractall (memo _), not (memo _)?"
    ] $ \text -> do
      query <- evalEither (parseQuery text)
      (items, metrics) <- compareQuery program query
      assert (Machine.metricCollections metrics > 0)
      let states search = [state | Reference.Found state <- search]
          table entry = (Reference.teComplete entry, Reference.teTruncated entry,
            Reference.teAnswers entry, Reference.teSet entry)
          metadata state = (Reference.ssFresh state, Reference.ssDynamic state,
            fmap table (Reference.ssTables state), Reference.ssOutput state, Reference.ssOutLen state)
      map metadata (states items) === map metadata (states (Reference.solveQuery program query))

prop_unsafe_output_growth_is_distinct_from_active_heap :: Property
prop_unsafe_output_growth_is_distinct_from_active_heap = unit $ do
  program <- load
  query <- evalEither (parseQuery "loud 12?")
  (items, metrics) <- compareQuery program query
  assert (Machine.metricCollections metrics > 0)
  Machine.metricTailCalls metrics === 0
  assert (Machine.metricMaxHeapCells metrics <= 16384)
  case [state | Reference.Found state <- items] of
    [state] -> do
      Reference.ssOutLen state === fromIntegral (fib 13)
      length (Reference.ssOutput state) === Reference.ssOutLen state
    _ -> failure

prop_cut_and_late_error_observations :: Property
prop_cut_and_late_error_observations = unit $ do
  program <- load
  forM_
    [ "(cut_after 13 F ; F = outer_alternative)?",
      "(outer 13 F, fail ; F = fallback)?",
      "once (fib 13 F, unknown)?",
      "not (fib 13 F, unknown)?",
      "findall F (fib 13 F, (true ; unknown)) Answers?",
      "(fib 13 F, unknown -> R = then ; R = otherwise)?",
      "X in 1..3, fib 13 F, (X = bad ; X = 2), label [X]?"
    ] $ \text -> do
      (_, metrics) <- compareText program text
      assert (Machine.metricCollections metrics > 0)

prop_delayed_contract_arguments_remain_live :: Property
prop_delayed_contract_arguments_remain_live = unit $ do
  program <- load
  forM_ ["badout X?", "missingout X?", "required X?"] $ \text -> do
    (items, metrics) <- compareText program text
    assert (Machine.metricCollections metrics > 0)
    Machine.metricTailCalls metrics === 0
    assert (not (null [problem | Reference.BranchError problem <- items]))

prop_older_answers_and_checkpoints_remain_independent :: Property
prop_older_answers_and_checkpoints_remain_independent = unit $ do
  program <- load
  query <- evalEither (parseQuery "(Tag = first ; Tag = second), outer 13 F?")
  initial <- evalEither (Machine.startMeasured program query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = observe query [retained]
      _ <- evalIO (evaluate (length (show before)))
      (following, final) <- evalEither (drain next)
      (repeated, _) <- evalEither (drain next)
      (allItems, _) <- evalEither (drain initial)
      assert (Machine.metricCollections (Machine.checkpointMetrics final) > 0)
      observe query [retained] === before
      observe query following === observe query repeated
      observe query (retained : following) === observe query allItems
      observe query allItems === observe query (Reference.solveQuery program query)
      -- The retained answer has immutable output and bindings after another
      -- branch restores its predecessor heap and repeatedly collects again.
      [Reference.ssOutLen state | Reference.Found state <- retained : following] === [1, 1]

machineGeneralReclaimGroup :: Group
machineGeneralReclaimGroup = Group "machine general active-branch reclamation"
  [ ("generated_scope_cut_constraint_contexts", prop_generated_scope_cut_constraint_contexts),
    ("non_tail_exponential_work_has_bounded_active_heap", prop_non_tail_exponential_work_has_bounded_active_heap),
    ("active_clp_metadata_survives_repeated_collection", prop_active_clp_metadata_survives_repeated_collection),
    ("dynamic_tables_and_freshness_survive_collection", prop_dynamic_tables_and_freshness_survive_collection),
    ("unsafe_output_growth_is_distinct_from_active_heap", prop_unsafe_output_growth_is_distinct_from_active_heap),
    ("cut_and_late_error_observations", prop_cut_and_late_error_observations),
    ("delayed_contract_arguments_remain_live", prop_delayed_contract_arguments_remain_live),
    ("older_answers_and_checkpoints_remain_independent", prop_older_answers_and_checkpoints_remain_independent)
  ]
