{-# LANGUAGE OverloadedStrings #-}

-- Free arguments and structured values exercise logical root preservation,
-- rather than relying on the scalar loop's absence of variable sharing.
module MachineStructuredTailTest (machineStructuredTailGroup) where

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

data Event
  = Answer String [Reference.OutputEvent]
  | Exhausted
  | Error SolveError
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
      Reference.BranchError err -> Error err
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete key

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load text = annotate text >> evalEither (Reference.loadProgramText text)

queryText :: String -> PropertyT IO Query
queryText text = annotate text >> evalEither (parseQuery text)

source :: String
source = unlines
  [ "<- notable.",
    "result 0 R <- R = done.",
    "result N R <- N > 0, M is N - 1, result M R.",
    "free 0 R.",
    "free N R <- N > 0, M is N - 1, free M R.",
    "carry 0 A A.",
    "carry N A R <- N > 0, M is N - 1, carry M A R.",
    "walk nil R <- R = done.",
    "walk [_ | Rest] R <- walk Rest R.",
    "grow 0 A A.",
    "grow N A R <- N > 0, M is N - 1, grow M (box A) R."
  ]

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
  _ <- evalIO (evaluate (length (show (observe query items))))
  pure (items, Machine.checkpointMetrics final)

compareQuery :: Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
compareQuery program query = do
  result@(items, _) <- run program query
  observe query items === observe query (Reference.solveQuery program query)
  observe query items === observe query (Machine.solveQuery program query)
  pure result

prop_generated_free_results :: Property
prop_generated_free_results = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 0 80))
  context <- forAll (Gen.element
    [ "result % R?", "free % R?", "free % R, R = done?",
      "X = R, free % X?", "X = R, result % X?",
      "(result % R, fail ; R = fallback)?",
      "result % R, (X = first ; X = second)?"
    ])
  program <- load source
  let replace [] = []
      replace ('%' : rest) = show count ++ replace rest
      replace (char : rest) = char : replace rest
  query <- queryText (replace context)
  _ <- compareQuery program query
  pure ()

genData :: Int -> Gen Term
genData depth
  | depth <= 0 = Gen.element [Var 1, Atom "leaf", IntLit 7, StrLit "kept"]
  | otherwise = Gen.choice
      [ genData 0,
        Compound "box" . (: []) <$> genData (depth - 1),
        Compound "pair" <$> sequence [genData (depth - 1), genData (depth - 1)],
        (`mkList` Nothing) <$> Gen.list (Range.linear 0 3) (genData (depth - 1))
      ]

-- The expected value is built independently from the generated input. The
-- reference comparison additionally checks exact answer naming and ordering.
prop_generated_structured_sharing :: Property
prop_generated_structured_sharing = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 0 80))
  value <- forAll (genData 3)
  bindLeaf <- forAll Gen.bool
  program <- load source
  let query = Query
        ([Compound "carry" [IntLit (fromIntegral count), value, Var 0]]
          ++ [Compound "unify" [Var 1, Atom "done"] | bindLeaf])
        [("R", 0), ("Leaf", 1)] 2
      expected (Var 1) | bindLeaf = Atom "done"
      expected (Compound name terms) = Compound name (map expected terms)
      expected term = term
  (items, _) <- compareQuery program query
  case [Reference.projectAnswer query state | Reference.Found state <- items] of
    [answer] -> do
      -- A free R may be represented solely as an alias by projection; all
      -- structured or subsequently ground values must remain observable.
      case expected value of
        Var _ -> pure ()
        term -> lookup "R" (Reference.answerBindings answer) === Just term
      Reference.answerResiduals answer === []
    _ -> failure

prop_generated_list_walker :: Property
prop_generated_list_walker = withTests 100 . property $ do
  values <- forAll (Gen.list (Range.linear 0 80) (genData 1))
  program <- load source
  let query = Query [Compound "walk" [mkList values Nothing, Var 0]] [("R", 0)] 2
  (items, _) <- compareQuery program query
  observe query items === [Answer "R = done" []]

prop_generated_growing_result :: Property
prop_generated_growing_result = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 0 60))
  program <- load source
  let query = Query [Compound "grow" [IntLit (fromIntegral count), Atom "seed", Var 0]] [("R", 0)] 1
      expected = iterate (\term -> Compound "box" [term]) (Atom "seed") !! count
  (items, _) <- compareQuery program query
  case [Reference.projectAnswer query state | Reference.Found state <- items] of
    [answer] -> lookup "R" (Reference.answerBindings answer) === Just expected
    _ -> failure

bounded :: Machine.Metrics -> PropertyT IO ()
bounded metrics = do
  assert (Machine.metricTailCalls metrics > 9000)
  assert (Machine.metricCollections metrics > 0)
  assert (Machine.metricMaxTasks metrics <= 32)
  assert (Machine.metricMaxChoices metrics <= 8)
  Machine.metricMaxScopes metrics === 0
  assert (Machine.metricMaxCutOwners metrics <= 4)
  assert (Machine.metricMaxHeapCells metrics <= 16384)
  assert (Machine.metricMaxTrailEntries metrics <= 8192)
  assert (Machine.metricMaxBindings metrics <= 4096)
  assert (Machine.metricMaxSubstitutions metrics <= 4096)

prop_bounded_free_and_structured_state :: Property
prop_bounded_free_and_structured_state = unit $ do
  program <- load source
  forM_
    [ ("result 10000 R?", [Answer "R = done" []]),
      ("carry 10000 (box Leaf) R, Leaf = done?", [Answer "Leaf = done, R = box done" []]),
      ("X = R, free 10000 X, R = done?", [Answer "X = done, R = done" []])
    ] $ \(text, expected) -> do
      query <- queryText text
      (items, metrics) <- run program query
      observe query items === expected
      bounded metrics

prop_repeated_structured_checkpoint :: Property
prop_repeated_structured_checkpoint = unit $ do
  program <- load source
  query <- queryText "carry 4000 (box Leaf) R, (Leaf = first ; Leaf = second)?"
  initial <- evalEither (Machine.startMeasured program query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = observe query [retained]
      before === [Answer "Leaf = first, R = box first" []]
      _ <- evalIO (evaluate (length (show before)))
      assert (Machine.metricCollections (Machine.checkpointMetrics next) > 0)
      (remaining, _) <- evalEither (drain next)
      (repeated, _) <- evalEither (drain next)
      (restarted, _) <- evalEither (drain initial)
      observe query remaining === [Answer "Leaf = second, R = box second" []]
      observe query repeated === observe query remaining
      observe query restarted === before ++ observe query remaining
      observe query [retained] === before

prop_declared_ground_structure_reuses :: Property
prop_declared_ground_structure_reuses = unit $ do
  program <- load $ unlines
    [ "<- notable.",
      "typed : semidet (int: <=) (list int: <=).",
      "typed 0 _.",
      "typed N Data <- N > 0, M is N - 1, typed M Data."
    ]
  query <- queryText "typed 4000 [1, 2, 3]?"
  (items, metrics) <- compareQuery program query
  observe query items === [Answer "true." []]
  assert (Machine.metricTailCalls metrics > 3000)
  assert (Machine.metricCollections metrics > 0)

prop_declared_nonground_return_obligations :: Property
prop_declared_nonground_return_obligations = unit $ do
  program <- load $ unlines
    [ "<- notable.",
      "out : semidet (int: <=) (int: =>).",
      "out 0 1.",
      "out N X <- N > 0, X = bad, M is N - 1, out M 1.",
      "checked : semidet (int: <=) (int: <=>).",
      "checked 0 1.",
      "checked N X <- N > 0, X = bad, M is N - 1, checked M 1.",
      "missing : semidet (int: <=) (int: =>).",
      "missing 0 X.",
      "missing N X <- N > 0, M is N - 1, missing M X."
    ]
  forM_ ["out", "checked"] $ \name -> do
    query <- queryText (name ++ " 1 X?")
    (items, _) <- compareQuery program query
    observe query items === [Error (SortError (name, 2) 2 SInt (Atom "bad"))]
  query <- queryText "missing 4 X?"
  (items, metrics) <- compareQuery program query
  assert (any isOutputError items)
  Machine.metricTailCalls metrics === 0
  where
    isOutputError (Reference.BranchError (OutputModeError ("missing", 2) 2 _)) = True
    isOutputError _ = False

prop_control_data_and_cut_fallback :: Property
prop_control_data_and_cut_fallback = unit $ do
  program <- load source
  query <- queryText "G = (H ; X = otherwise), H = (true -> X = then), carry 4000 G R, call R?"
  _ <- compareQuery program query
  -- Both a query cut and an explicitly foreign marker may travel as data.
  -- The source is cut-free, but these arguments cannot justify retirement.
  forM_
    [ Query
        [Compound "carry" [IntLit 20, Atom "!", Var 0], Compound "call" [Var 0]]
        [("R", 0)] 1,
      Query [Compound "carry" [IntLit 20, Compound "box" [Atom "!"], Var 0]]
        [("R", 0)] 1
    ] $ \cutQuery -> do
      (_, metrics) <- compareQuery program cutQuery
      Machine.metricTailCalls metrics === 0

prop_scopes_choices_and_contracts_still_fallback :: Property
prop_scopes_choices_and_contracts_still_fallback = unit $ do
  program <- load $ source ++ unlines
    [ "required : det (int: <=) (any: <=>).",
      "required 0 _ <- fail.",
      "required N R <- N > 0, M is N - 1, required M R.",
      "many 0 first.", "many 0 second.",
      "many N R <- N > 0, M is N - 1, many M R."
    ]
  forM_
    [ "(result 20 R ; R = alternative)?",
      "once (result 20 R)?", "call (result 20 R)?",
      "not (result 20 R, fail)?",
      "(result 20 R -> X = yes ; X = no)?",
      "findall R (result 20 R) L?"
    ] $ \text -> do
      query <- queryText text
      (_, metrics) <- compareQuery program query
      assert (Machine.metricTailCalls metrics > 0)
  requiredQuery <- queryText "required 4 R?"
  (_, requiredMetrics) <- compareQuery program requiredQuery
  Machine.metricTailCalls requiredMetrics === 0
  -- At the base case, surviving alternatives must still yield in order.
  query <- queryText "many 30 R?"
  (items, _) <- compareQuery program query
  observe query items === [Answer "R = first" [], Answer "R = second" []]

prop_explicit_fuel_preserves_free_arguments :: Property
prop_explicit_fuel_preserves_free_arguments = unit $ do
  program <- load source
  let environment = Reference.mkEnv program
      state = Reference.initialState 2
      query = Query [] [("R", 0), ("Leaf", 1)] 2
  forM_ [0 .. 5] $ \fuel -> forM_
    [ [Compound "result" [IntLit 8, Var 0]],
      [Compound "carry" [IntLit 8, Compound "box" [Var 1], Var 0]],
      [Compound "walk" [mkList [Var 1, Atom "a"] Nothing, Var 0]]
    ] $ \goals -> do
      initial <- evalEither (Machine.startGoals environment fuel state goals)
      (items, final) <- evalEither (drain initial)
      observe query items === observe query (Reference.solveGoals environment fuel state goals)
      Machine.metricTailCalls (Machine.checkpointMetrics final) === 0

machineStructuredTailGroup :: Group
machineStructuredTailGroup = Group "machine structured tail reuse"
  [ ("generated_free_results", prop_generated_free_results),
    ("generated_structured_sharing", prop_generated_structured_sharing),
    ("generated_list_walker", prop_generated_list_walker),
    ("generated_growing_result", prop_generated_growing_result),
    ("bounded_free_and_structured_state", prop_bounded_free_and_structured_state),
    ("repeated_structured_checkpoint", prop_repeated_structured_checkpoint),
    ("declared_ground_structure_reuses", prop_declared_ground_structure_reuses),
    ("declared_nonground_return_obligations", prop_declared_nonground_return_obligations),
    ("control_data_and_cut_fallback", prop_control_data_and_cut_fallback),
    ("scopes_choices_and_contracts_still_fallback", prop_scopes_choices_and_contracts_still_fallback),
    ("explicit_fuel_preserves_free_arguments", prop_explicit_fuel_preserves_free_arguments)
  ]
