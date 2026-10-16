{-# LANGUAGE OverloadedStrings #-}

-- Reusing a heap argument graph must preserve reference normalization at
-- observable shallow-syntax boundaries. The ordinary ground-list path should
-- avoid copying every remaining suffix into each recursive activation.
module MachineGraphReuseTest (machineGraphReuseGroup) where

import Control.Monad (forM_)
import qualified Data.IntMap.Strict as IM
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP (emptyStore, stSubst)
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program (Program)
import Infera.Syntax
import Infera.Unify (canonicalize, deepWalk, emptySubst)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

canonicalTerms :: Query -> [Term] -> [Term]
canonicalTerms query terms = case fst (canonicalize emptySubst combined) of
  Compound _ roots -> drop (length names) roots
  _ -> error "canonicalizing a compound changed its constructor"
  where
    names = map (Var . snd) (queryNames query)
    combined = Compound "$graph_observations" (names ++ terms)

canonicalError :: Query -> SolveError -> SolveError
canonicalError query problem = case problem of
  InstantiationError term -> InstantiationError (canonical term)
  ExpectedInteger term -> ExpectedInteger (canonical term)
  ExpectedNumber term -> ExpectedNumber (canonical term)
  ModeError key index term -> ModeError key index (canonical term)
  OutputModeError key index term -> OutputModeError key index (canonical term)
  SortError key index sort term -> SortError key index sort (canonical term)
  CLPTypeError term -> CLPTypeError (canonical term)
  UnboundedDomain term -> UnboundedDomain (canonical term)
  TypeError description term -> TypeError description (canonical term)
  other -> other
  where
    canonical term = case canonicalTerms query [term] of
      [result] -> result
      _ -> error "canonicalization changed the number of roots"

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent]
  | Error SolveError | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
         in Answer (zip (map fst bindings) (canonicalTerms query (map snd bindings)))
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
      Reference.BranchError problem -> Error (canonicalError query problem)
      Reference.BranchExhausted -> Exhausted
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete (fst (canonicalize emptySubst key))

compareQuery :: Program -> Query -> PropertyT IO Reference.Search
compareQuery program query = do
  let actual = Machine.solveQuery program query
  observe query actual === observe query (Reference.solveQuery program query)
  pure actual

compareText :: Program -> String -> PropertyT IO Reference.Search
compareText program source = do
  annotate source
  query <- evalEither (parseQuery source)
  compareQuery program query

programSource :: String
programSource = unlines
  [ "<- notable.",
    "copy X X.",
    "swap (pair X Y) (pair Y X).",
    "bad X <- str_length X N.",
    "check X <- str_atom X N.",
    "length nil 0.",
    "length [_ | Tail] N <- length Tail M, N is M + 1.",
    "eval : nondet unsafe (any: <=>).", "eval Goal <- Goal.",
    "boxeval : nondet unsafe (any: <=>).", "boxeval (box Goal) <- Goal."
  ]

load :: PropertyT IO Program
load = evalEither (Reference.loadProgramText programSource)

genData :: Int -> Gen Term
genData depth
  | depth <= 0 = Gen.choice
      [ Var <$> Gen.int (Range.linear 0 2),
        Gen.element [Atom "leaf", IntLit 7, StrLit "kept", CharLit '\x03bb']
      ]
  | otherwise = Gen.frequency
      [ (4, genData 0),
        (2, Compound "box" . (: []) <$> genData (depth - 1)),
        (2, Compound "pair" <$> Gen.list (Range.singleton 2) (genData (depth - 1))),
        (2, (`mkList` Nothing) <$> Gen.list (Range.linear 0 4) (genData (depth - 1)))
      ]

prop_generated_structured_free_graphs :: Property
prop_generated_structured_free_graphs = withTests 300 . property $ do
  program <- load
  value <- forAll (genData 3)
  alias <- forAll Gen.bool
  bindBefore <- forAll Gen.bool
  bindAfter <- forAll Gen.bool
  let prefix = [Compound "unify" [Var 2, Var 1] | alias]
        ++ [Compound "unify" [Var 1, Atom "before"] | bindBefore]
      calls = [Compound "copy" [value, Var 3], Compound "copy" [Var 3, Var 4]]
      suffix = [Compound "unify" [Var 2, Atom "after"] | bindAfter]
      query = Query (prefix ++ calls ++ suffix)
        [("A", 0), ("B", 1), ("C", 2), ("Result", 3), ("Again", 4)] 5
  items <- compareQuery program query
  forM_ [state | Reference.Found state <- items] $ \state -> do
    let substitution = stSubst (Reference.ssStore state)
    deepWalk substitution (Var 3) === deepWalk substitution value
    deepWalk substitution (Var 4) === deepWalk substitution value

prop_generated_nested_bound_error_syntax :: Property
prop_generated_nested_bound_error_syntax = withTests 200 . property $ do
  program <- load
  value <- forAll (genData 2)
  let wrapped = Compound "wrapper" [value]
      query = Query
        [Compound "unify" [Var 1, Atom "bound"], Compound "bad" [wrapped]]
        [("A", 0), ("B", 1), ("C", 2)] 3
  items <- compareQuery program query
  let expected = deepWalk (IM.singleton 1 (Atom "bound")) wrapped
  observe query items === [Error (TypeError "string" expected)]

prop_shallow_errors_preserve_nested_bindings_and_alias_ids :: Property
prop_shallow_errors_preserve_nested_bindings_and_alias_ids = unit $ do
  program <- load
  forM_
    [ "A = done, bad (box A)?",
      "A = B, bad (box B)?",
      "A = (box done), bad (box A)?",
      "A = done, check (pair A A)?",
      "A = B, B = done, bad [A, B]?"
    ] $ \source -> compareText program source >> pure ()
  -- Accepted caller states may direct an alias toward a larger logical ID;
  -- graph reuse must preserve that representative in the shallow error term.
  let environment = Reference.mkEnv program
      state = (Reference.initialState 2)
        {Reference.ssStore = emptyStore {stSubst = IM.singleton 0 (Var 1)}}
      goals = [Compound "bad" [Compound "box" [Var 0]]]
      query = Query goals [("A", 0), ("B", 1)] 2
  observe query (Machine.solveGoals environment 20 state goals)
    === observe query (Reference.solveGoals environment 20 state goals)
  observe query (Machine.solveGoals environment 20 state goals)
    === [Error (TypeError "string" (Compound "box" [Var 1]))]

prop_control_shaped_data_is_normalized_before_user_call :: Property
prop_control_shaped_data_is_normalized_before_user_call = unit $ do
  program <- load
  forM_
    [ "C = (true -> X = then), eval (C ; X = otherwise)?",
      "C = (true -> X = then), boxeval (box (C ; X = otherwise))?",
      "C = (true -> X = then), D = (C ; X = otherwise), eval D?",
      "C = (true -> fail), eval (C ; X = otherwise)?",
      "C = (true -> fail), boxeval (box (C ; X = otherwise))?"
    ] $ \source -> compareText program source >> pure ()
  query <- evalEither (parseQuery "C = (true -> X = then), eval (C ; X = otherwise)?")
  items <- compareQuery program query
  [deepWalk (stSubst (Reference.ssStore state)) (Var 1) | Reference.Found state <- items] === [Atom "then"]
  -- Literal integer owners are special only after predicate argument
  -- normalization; the otherwise identical raw variable form is ordinary
  -- unknown $cut/1 syntax when evaluated directly outside a user call.
  let queryCut = Query
        [ Compound "unify" [Var 0, IntLit (-1)],
          Compound "eval" [Compound ";"
            [ Compound "$cut" [Var 0], Compound "unify" [Var 1, Atom "otherwise"] ]]
        ] [("Owner", 0), ("X", 1)] 2
  cutItems <- compareQuery program queryCut
  [problem | Reference.BranchError problem <- cutItems] === []
  length [() | Reference.Found _ <- cutItems] === 1

-- This is an ordinary non-tail recursion: the addition must run on return.
-- A copied remaining suffix at every call needs quadratic heap cells; graph
-- reuse needs only the original list and a fixed amount per activation.
prop_non_tail_ground_list_uses_linear_heap_cells :: Property
prop_non_tail_ground_list_uses_linear_heap_cells = unit $ do
  program <- load
  let count = 512 :: Int
      query = Query [Compound "length" [mkList (replicate count (Atom "item")) Nothing, Var 0]] [("N", 0)] 1
  initial <- evalEither (Machine.startMeasured program query)
  (items, final) <- evalEither (drain initial)
  Reference.summarizeSearch query items === Reference.solveAll program query
  [deepWalk (stSubst (Reference.ssStore state)) (Var 0) | Reference.Found state <- items] === [IntLit (fromIntegral count)]
  let metrics = Machine.checkpointMetrics final
  annotateShow metrics
  Machine.metricTailCalls metrics === 0
  assert (Machine.metricMaxTasks metrics >= count)
  assert (Machine.metricMaxHeapCells metrics <= 64 * count + 2048)

prop_reused_graph_checkpoints_remain_independent :: Property
prop_reused_graph_checkpoints_remain_independent = unit $ do
  program <- load
  query <- evalEither (parseQuery "copy (pair A A) R, (A = first ; A = second)?")
  initial <- evalEither (Machine.start program query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      (following, _) <- evalEither (drain next)
      (repeated, _) <- evalEither (drain next)
      (allItems, _) <- evalEither (drain initial)
      observe query following === observe query repeated
      observe query (retained : following) === observe query allItems
      observe query allItems === observe query (Reference.solveQuery program query)

drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Checkpoint)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> Right ([], checkpoint)
    Machine.Yield item next -> do
      (rest, final) <- drain next
      Right (item : rest, final)

machineGraphReuseGroup :: Group
machineGraphReuseGroup = Group "machine argument graph reuse"
  [ ("generated_structured_free_graphs", prop_generated_structured_free_graphs),
    ("generated_nested_bound_error_syntax", prop_generated_nested_bound_error_syntax),
    ("shallow_errors_preserve_nested_bindings_and_alias_ids", prop_shallow_errors_preserve_nested_bindings_and_alias_ids),
    ("control_shaped_data_is_normalized_before_user_call", prop_control_shaped_data_is_normalized_before_user_call),
    ("non_tail_ground_list_uses_linear_heap_cells", prop_non_tail_ground_list_uses_linear_heap_cells),
    ("reused_graph_checkpoints_remain_independent", prop_reused_graph_checkpoints_remain_independent)
  ]
