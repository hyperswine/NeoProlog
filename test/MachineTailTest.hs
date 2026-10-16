{-# LANGUAGE OverloadedStrings #-}

-- Tail reuse is deliberately conservative. These tests check both its useful
-- constant-space case and the observable behavior of cases left on the normal
-- control path. The million-iteration residency gate lives in machine-tail.
module MachineTailTest (machineTailGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program (Program)
import Infera.Syntax

data Event
  = Answer String [Reference.OutputEvent]
  | Exhausted
  | Error String
  | Cut Int
  | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
         in Answer (Reference.showAnswer answer) (Reference.answerOutput answer)
      Reference.BranchExhausted -> Exhausted
      Reference.BranchError err -> Error (show err)
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete key

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText text = annotate text >> evalEither (parseQuery text)

loopSource :: String
loopSource = unlines
  [ "<- notable.",
    "down 0.",
    "down N <- N > 0, M is N - 1, down M."
  ]

-- Retain the final yielded checkpoint as well as draining its continuation.
-- A successful first answer alone would miss failures in trailing retries.
drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Checkpoint)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], checkpoint)
    Machine.Yield item next -> do
      (rest, final) <- drain next
      pure (item : rest, final)

run :: Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
run program query = do
  initial <- evalEither (Machine.startMeasured program query)
  (items, final) <- evalEither (drain initial)
  -- Force observations while both initial and final immutable checkpoints
  -- remain reachable, so later resumes really test independent ownership.
  _ <- evalIO (evaluate (length (show (observe query items))))
  pure (items, Machine.checkpointMetrics final)

compareQuery :: Program -> Query -> PropertyT IO Machine.Metrics
compareQuery program query = do
  (items, metrics) <- run program query
  observe query items === observe query (Reference.solveQuery program query)
  observe query items === observe query (Machine.solveQuery program query)
  pure metrics

prop_generated_small_tail_parity :: Property
prop_generated_small_tail_parity = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 0 80))
  context <- forAll (Gen.element
    [ "down %?",
      "down %, X = done?",
      "(down %, X = first ; X = second)?",
      "(down %, fail ; X = fallback)?"
    ])
  program <- load loopSource
  let replace [] = []
      replace ('%' : rest) = show count ++ replace rest
      replace (char : rest) = char : replace rest
  query <- queryText (replace context)
  _ <- compareQuery program query
  pure ()

prop_bounded_tail_machine_state :: Property
prop_bounded_tail_machine_state = unit $ do
  program <- load loopSource
  query <- queryText "down 10000?"
  (items, metrics) <- run program query
  observe query items === [Answer "true." []]
  assert (Machine.metricCalls metrics >= 10001)
  assert (Machine.metricTailCalls metrics > 9000)
  assert (Machine.metricCollections metrics > 0)
  -- These are generous bounds around the collection threshold, not timing
  -- assertions. Every retained map and the cut-owner chain is counted.
  assert (Machine.metricMaxTasks metrics <= 32)
  assert (Machine.metricMaxChoices metrics <= 8)
  Machine.metricMaxScopes metrics === 0
  assert (Machine.metricMaxCutOwners metrics <= 4)
  assert (Machine.metricMaxHeapCells metrics <= 16384)
  assert (Machine.metricMaxTrailEntries metrics <= 8192)
  assert (Machine.metricMaxBindings metrics <= 4096)
  assert (Machine.metricMaxSubstitutions metrics <= 4096)
  assert (Machine.metricMaxConstants metrics <= 4096)
  assert (Machine.metricMaxFunctors metrics <= 64)

prop_unmeasured_tail_execution :: Property
prop_unmeasured_tail_execution = unit $ do
  program <- load loopSource
  query <- queryText "down 10000?"
  initial <- evalEither (Machine.start program query)
  (items, final) <- evalEither (drain initial)
  observe query items === [Answer "true." []]
  -- Instrumentation must not be necessary to make recursive state strict.
  -- Residency for this path is measured separately by the fresh-process
  -- runner's --unmeasured mode; counters intentionally remain disabled.
  let metrics = Machine.checkpointMetrics final
  Machine.metricCalls metrics === 0
  Machine.metricTailCalls metrics === 0
  Machine.metricCollections metrics === 0

prop_retained_checkpoints_after_collection :: Property
prop_retained_checkpoints_after_collection = unit $ do
  program <- load loopSource
  query <- queryText "down 4000, (X = first ; X = second)?"
  initial <- evalEither (Machine.startMeasured program query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = observe query [retained]
      before === [Answer "X = first" []]
      _ <- evalIO (evaluate (length (show before)))
      assert (Machine.metricCollections (Machine.checkpointMetrics next) > 0)
      (remaining, _) <- evalEither (drain next)
      (repeated, _) <- evalEither (drain next)
      (restarted, _) <- evalEither (drain initial)
      observe query remaining === [Answer "X = second" []]
      observe query repeated === observe query remaining
      observe query restarted === before ++ observe query remaining
      observe query [retained] === before

prop_live_roots_and_raw_control_after_collection :: Property
prop_live_roots_and_raw_control_after_collection = unit $ do
  program <- load $ loopSource ++ unlines
    [ "boxed X <- X = (box Y), down 4000, Y = done.",
      "share X Y <- X = Y, down 4000, Y = done."
    ]
  forM_
    [ "X = (box Y), down 4000, Y = done?",
      "boxed X?",
      "share X Y?",
      "G = (H ; X = otherwise), H = (true -> X = then), down 4000, call G?"
    ] $ \text -> do
      query <- queryText text
      _ <- compareQuery program query
      pure ()

prop_conservative_tail_fallbacks :: Property
prop_conservative_tail_fallbacks = unit $ do
  -- Contracts, live choices and rollback scopes must preserve their complete
  -- ordinary control semantics even when a clause ends with a recursive call.
  let source = loopSource ++ unlines
        [ "outer N X <- down N, X = first.",
          "outer _ second.",
          "failed N X <- down N, fail.",
          "failed _ fallback.",
          "answers 0 a.", "answers 0 a.", "answers 0 b.",
          "answers N X <- N > 0, M is N - 1, answers M X.",
          "required : det (int: <=).",
          "required 0 <- fail.",
          "required N <- N > 0, M is N - 1, required M.",
          "out : semidet (int: <=) (int: =>).",
          "out 0 X.",
          "out N X <- N > 0, M is N - 1, out M X.",
          "cutloop : unsafe.",
          "cutloop 0.",
          "cutloop N <- N > 0, M is N - 1, !, cutloop M.",
          "cutloop fallback.",
          "tabled : table.",
          "tabled 0.",
          "tabled N <- N > 0, M is N - 1, tabled M.",
          "fact : dynamic."
        ]
  program <- load source
  forM_
    [ "required 4?", "out 4 X?", "cutloop 20?", "(cutloop 20 ; X = outer)?", "tabled 20?"
    ] $ \text -> do
      query <- queryText text
      metrics <- compareQuery program query
      Machine.metricTailCalls metrics === 0
  -- Independently owned frozen alternatives and scopes now permit collection
  -- without dropping their rollback state or suppressing their observations.
  forM_
    [ "outer 20 X?", "failed 20 X?",
      "once (down 20), X = done?", "not (down 20, fail)?",
      "(down 20 -> X = yes ; X = no)?", "call (down 20)?",
      "findall X (down 20, (X = a ; X = b)) L?",
      "X in 1..3, down 20, label [X]?",
      "X in 1..3, Y in 1..3, X #< Y, down 20, label [X, Y]?",
      "assert (fact seed), down 20, fact X?"
    ] $ \text -> do
      query <- queryText text
      metrics <- compareQuery program query
      assert (Machine.metricTailCalls metrics > 0)
  -- The deterministic prefix can now transfer a free result variable. Choices
  -- created at the base case still preserve duplicate answers and their order.
  answersQuery <- queryText "answers 20 X?"
  answersMetrics <- compareQuery program answersQuery
  Machine.metricTailCalls answersMetrics === 20

prop_explicit_fuel_still_bounds_tail_calls :: Property
prop_explicit_fuel_still_bounds_tail_calls = unit $ do
  program <- load loopSource
  let environment = Reference.mkEnv program
      state = Reference.initialState 1
      query = Query [] [("X", 0)] 1
  forM_ [0 .. 5] $ \fuel -> forM_
    [ [Compound "down" [IntLit 8]],
      [Compound ";" [Compound "down" [IntLit 8], Compound "unify" [Var 0, Atom "fallback"]]],
      [Compound "down" [IntLit 1], Compound "down" [IntLit 1]]
    ] $ \goals -> do
      initial <- evalEither (Machine.startGoals environment fuel state goals)
      (items, final) <- evalEither (drain initial)
      observe query items === observe query (Reference.solveGoals environment fuel state goals)
      Machine.metricTailCalls (Machine.checkpointMetrics final) === 0

machineTailGroup :: Group
machineTailGroup = Group "machine tail reuse"
  [ ("generated_small_tail_parity", prop_generated_small_tail_parity),
    ("bounded_tail_machine_state", prop_bounded_tail_machine_state),
    ("unmeasured_tail_execution", prop_unmeasured_tail_execution),
    ("retained_checkpoints_after_collection", prop_retained_checkpoints_after_collection),
    ("live_roots_and_raw_control_after_collection", prop_live_roots_and_raw_control_after_collection),
    ("conservative_tail_fallbacks", prop_conservative_tail_fallbacks),
    ("explicit_fuel_still_bounds_tail_calls", prop_explicit_fuel_still_bounds_tail_calls)
  ]
