{-# LANGUAGE OverloadedStrings #-}

-- A pure noncommitting activation can retire with parked retries: each retry
-- owns its original frame and heap. Committing activations must retain their
-- success barrier when an internal alternative remains pending.
module MachineInternalTailTest (machineInternalTailGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Engine.Reference as Reference
import Infera.Error (SolveError (..))
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program (Program)
import Infera.Syntax

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

source :: String
source = unlines
  [ "<- notable.",
    "step N.", "step N <- X is bad N.",
    "walk 0 done.",
    "walk N R <- N > 0, step N, M is N - 1, walk M R.",
    "range N N [N].",
    "range I N [I | T] <- I < N, I1 is I + 1, range I1 N T.",
    "range_walk 0 done.",
    "range_walk N R <- N > 0, range 1 3 L, M is N - 1, range_walk M R.",
    "committed : semidet (int: <=) (int: <=).",
    "committed 0 _.",
    "committed N R <- N > 0, step N, M is N - 1, committed M R."
  ]

load :: PropertyT IO Program
load = evalEither (Reference.loadProgramText source)

data Event
  = Answer Reference.Answer | Error SolveError | Exhausted | Cut Int | Incomplete Term
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

prop_generated_internal_choices_preserve_order_and_errors :: Property
prop_generated_internal_choices_preserve_order_and_errors = withTests 150 . property $ do
  program <- load
  count <- forAll (Gen.int (Range.linear 0 50))
  context <- forAll (Gen.element
    [ "walk % R?", "once (walk % R)?",
      "(walk % R ; R = fallback)?",
      "findall R (walk % R) Answers?",
      "not (walk % R, fail)?",
      "(walk % R -> R = done ; R = fallback)?"
    ])
  let replace [] = []
      replace ('%' : rest) = show count ++ replace rest
      replace (character : rest) = character : replace rest
  query <- evalEither (parseQuery (replace context))
  _ <- compareQuery program query
  pure ()

prop_late_error_order_has_independent_model :: Property
prop_late_error_order_has_independent_model = withTests 100 . property $ do
  program <- load
  count <- forAll (Gen.int (Range.linear 0 60))
  query <- evalEither (parseQuery ("walk " ++ show count ++ " R?"))
  (items, _) <- compareQuery program query
  [Reference.showAnswer (Reference.projectAnswer query state) | Reference.Found state <- items] === ["R = done"]
  [problem | Reference.BranchError problem <- items] ===
    [ExpectedNumber (Compound "bad" [IntLit (fromIntegral index)]) | index <- [1 .. count]]

prop_generated_pending_failing_range_retry :: Property
prop_generated_pending_failing_range_retry = withTests 100 . property $ do
  program <- load
  count <- forAll (Gen.int (Range.linear 0 80))
  query <- evalEither (parseQuery ("range_walk " ++ show count ++ " R?"))
  (items, _) <- compareQuery program query
  [Reference.showAnswer (Reference.projectAnswer query state) | Reference.Found state <- items] === ["R = done"]
  [problem | Reference.BranchError problem <- items] === []

prop_parked_choices_do_not_grow_active_return_frames :: Property
prop_parked_choices_do_not_grow_active_return_frames = unit $ do
  program <- load
  let count = 1000 :: Int
  forM_ ["walk", "range_walk"] $ \predicate -> do
    query <- evalEither (parseQuery (predicate ++ " " ++ show count ++ " R?"))
    (items, metrics) <- compareQuery program query
    annotateShow metrics
    [Reference.showAnswer (Reference.projectAnswer query state) | Reference.Found state <- items] === ["R = done"]
    assert (Machine.metricMaxChoices metrics >= count)
    assert (Machine.metricMaxTasks metrics <= 24)
    assert (Machine.metricMaxCutOwners metrics <= 8)
    assert (Machine.metricTailCalls metrics >= count - 4)
    assert (Machine.metricCollections metrics > 0)
    -- Frozen retries legitimately grow with this workload. The active heap
    -- and continuation frame bound is distinct from their retained snapshots.
    assert (Machine.metricMaxHeapCells metrics <= 4096)

prop_committing_parent_keeps_internal_success_barrier :: Property
prop_committing_parent_keeps_internal_success_barrier = unit $ do
  program <- load
  query <- evalEither (parseQuery "committed 30 7?")
  (items, metrics) <- compareQuery program query
  [problem | Reference.BranchError problem <- items] === []
  length [() | Reference.Found _ <- items] === 1
  -- Eliding these parents despite their pending step retry would expose the
  -- otherwise discarded late errors after the first successful result.
  Machine.metricTailCalls metrics === 0

prop_parked_retry_checkpoints_resume_independently :: Property
prop_parked_retry_checkpoints_resume_independently = unit $ do
  program <- load
  query <- evalEither (parseQuery "walk 120 R?")
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

machineInternalTailGroup :: Group
machineInternalTailGroup = Group "machine tail calls with parked internal retries"
  [ ("generated_internal_choices_preserve_order_and_errors", prop_generated_internal_choices_preserve_order_and_errors),
    ("late_error_order_has_independent_model", prop_late_error_order_has_independent_model),
    ("generated_pending_failing_range_retry", prop_generated_pending_failing_range_retry),
    ("parked_choices_do_not_grow_active_return_frames", prop_parked_choices_do_not_grow_active_return_frames),
    ("committing_parent_keeps_internal_success_barrier", prop_committing_parent_keeps_internal_success_barrier),
    ("parked_retry_checkpoints_resume_independently", prop_parked_retry_checkpoints_resume_independently)
  ]
