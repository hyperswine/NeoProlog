{-# LANGUAGE OverloadedStrings #-}

-- Native CLP keeps one complete persistent store beside its reversible heap.
-- Compare both the public ordered stream and independent finite models; direct
-- backend tests also inspect all scheduler metadata after every transaction.
module MachineCLPTest (machineCLPGroup) where

import Control.Monad (forM_)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (sort)
import GHC.Float (castDoubleToWord64)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.CLP as Native
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program (Program, buildProgram)
import Infera.Syntax
import Infera.Unify (canonicalize, deepWalk, emptySubst)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

canonical :: Query -> [Term] -> [Term]
canonical query terms = case fst (canonicalize emptySubst combined) of
  Compound _ roots -> drop (length names) roots
  _ -> error "canonicalization changed the root constructor"
  where
    names = map (Var . snd) (queryNames query)
    combined = Compound "$clp_observations" (names ++ terms)

canonicalError :: Query -> SolveError -> SolveError
canonicalError query err = case err of
  InstantiationError t -> InstantiationError (norm t)
  ExpectedInteger t -> ExpectedInteger (norm t)
  ExpectedNumber t -> ExpectedNumber (norm t)
  ModeError key i t -> ModeError key i (norm t)
  OutputModeError key i t -> OutputModeError key i (norm t)
  SortError key i sortName t -> SortError key i sortName (norm t)
  CLPTypeError t -> CLPTypeError (norm t)
  UnboundedDomain t -> UnboundedDomain (norm t)
  TypeError description t -> TypeError description (norm t)
  other -> other
  where
    norm t = case canonical query [t] of
      [result] -> result
      _ -> error "canonicalization changed the number of roots"

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent]
  | Exhausted | Error SolveError | Marker Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
         in Answer (zip (map fst bindings) (canonical query (map snd bindings)))
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
      Reference.BranchExhausted -> Exhausted
      Reference.BranchError err -> Error (canonicalError query err)
      Reference.CutMarker owner -> Marker owner
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

emptyProgram :: Program
emptyProgram = buildProgram []

found :: Reference.Search -> [Reference.SolverState]
found items = [state | Reference.Found state <- items]

values :: [VarId] -> Reference.SolverState -> [Term]
values variables state = map (deepWalk (stSubst (Reference.ssStore state)) . Var) variables

noIssues :: Reference.Search -> PropertyT IO ()
noIssues items = do
  [err | Reference.BranchError err <- items] === []
  [() | Reference.BranchExhausted <- items] === []

app :: String -> [Term] -> Term
app = Compound

list :: [Term] -> Term
list xs = mkList xs Nothing

domain :: Term -> Integer -> Integer -> Term
domain term lo hi = app "in" [term, app "range" [IntLit lo, IntLit hi]]

-- This model evaluates integer arithmetic directly, never the CLP solver.
prop_bounded_reification_abs_and_distinct :: Property
prop_bounded_reification_abs_and_distinct = withTests 300 . property $ do
  lo <- forAll (Gen.integral (Range.linear (-3) 0))
  hi <- forAll (Gen.integral (Range.linear 0 3))
  hole <- forAll (Gen.integral (Range.linear (-3) 3))
  cap <- forAll (Gen.integral (Range.linear 0 5))
  distinct <- forAll Gen.bool
  let x = Var 0; y = Var 1; truth = Var 2; distance = Var 3
      goals =
        [ domain (list [x, y]) lo hi,
          app "fd_ne" [x, IntLit hole],
          app "reify" [app "fd_lt" [x, y], truth],
          app "int_eq" [distance, app "abs" [app "minus" [x, y]]],
          app "fd_le" [distance, IntLit cap]
        ] ++ [app "all_distinct" [list [x, y]] | distinct]
          ++ [app "label" [list [x, y, truth, distance]]]
      query = Query goals [("X", 0), ("Y", 1), ("B", 2), ("D", 3)] 4
      expected = sort
        [map IntLit [a, b, if a < b then 1 else 0, abs (a - b)]
        | a <- [lo .. hi], b <- [lo .. hi], a /= hole,
          not distinct || a /= b, abs (a - b) <= cap]
  items <- compareQuery emptyProgram query
  noIssues items
  sort (map (values [0, 1, 2, 3]) (found items)) === expected

prop_bounded_branch_and_bound_model :: Property
prop_bounded_branch_and_bound_model = withTests 300 . property $ do
  lo <- forAll (Gen.integral (Range.linear (-3) 0))
  hi <- forAll (Gen.integral (Range.linear 0 3))
  hole <- forAll (Gen.integral (Range.linear (-3) 3))
  factor <- forAll (Gen.integral (Range.linear (-2) 2))
  limit <- forAll (Gen.integral (Range.linear (-4) 4))
  let x = Var 0; y = Var 1; cost = Var 2
      goals =
        [ domain (list [x, y]) lo hi,
          app "fd_ne" [x, IntLit hole],
          app "fd_lt" [x, y],
          app "fd_le" [app "plus" [x, y], IntLit limit],
          app "int_eq" [cost, app "plus"
            [app "abs" [app "minus" [x, y]], app "mul" [IntLit factor, x]]],
          app "labeling" [list [app "min" [cost]], list [x, y]]
        ]
      query = Query goals [("X", 0), ("Y", 1), ("Cost", 2)] 3
      solutions = [(a, b, abs (a - b) + factor * a)
        | a <- [lo .. hi], b <- [lo .. hi], a /= hole, a < b, a + b <= limit]
  items <- compareQuery emptyProgram query
  noIssues items
  case (solutions, map (values [0, 1, 2]) (found items)) of
    ([], []) -> success
    (_ : _, [[IntLit a, IntLit b, IntLit score]]) -> do
      assert ((a, b, score) `elem` solutions)
      score === minimum [n | (_, _, n) <- solutions]
    other -> annotateShow other >> failure

prop_aliases_domains_and_clause_retries :: Property
prop_aliases_domains_and_clause_retries = unit $ do
  program <- evalEither . Reference.loadProgramText $ unlines
    [ "choose (pair X X) rejected.",
      "choose (pair X Y) accepted.",
      "typed : unsafe.",
      "typed X <- X = 1, X = bad.",
      "typed 2.",
      "hidden _ X.",
      "fresh X."
    ]
  forM_
    [ "X = Y, Y in 1..4, Y #!= 2, X #> 1?",
      "Y in 1..4, Y #!= 2, X = Y, X #> 1?",
      "[X, Y] in 1..3, X #!= Y, choose (pair X Y) Result, label [X, Y]?",
      "X in 1..3, typed X?",
      "X in 1..3, ((pair Y X) = (pair 7 bad) ; Y = 8), label [X]?",
      "findall X (hidden ignored X) L, fresh Y, L = [Y], Y in 1..3?",
      "findall X (hidden ignored X) L, fresh Y, L = [Y], Y in 1..3, label [Y]?"
    ] $ \source -> compareText program source >> pure ()

prop_nested_subsearch_complete_store :: Property
prop_nested_subsearch_complete_store = unit $ do
  forM_
    [ "[X, Y] in 1..3, X #< Y, once (X = 1 ; X = 2), label [X, Y]?",
      "[X, Y] in 1..3, X #< Y, not (X = 2, Y = 1), label [X, Y]?",
      "[X, Y] in 1..3, X #< Y, ((X = 2, Y = 1) -> fail ; true), label [X, Y]?",
      "[X, Y] in 1..3, X #< Y, (X = 2 -> true ; X = 1), label [X, Y]?",
      "[X, Y] in 1..3, X #< Y, findall (pair X Y) (label [X, Y]) L, label [X, Y]?",
      "[X, Y] in 1..3, reify (X #< Y) B, findall B (label [X, Y, B]) L, B = 0, label [X, Y]?",
      "X in 1..3, once ((X = bad ; X = 2)), label [X]?",
      "X in 1..3, not ((X = bad ; X = 2)), label [X]?",
      "X in 1..3, ((X = bad ; X = 2) -> write X ; write no), label [X]?",
      "X in 1..3, findall X ((X = bad ; label [X])) L?"
    ] $ \source -> compareText emptyProgram source >> pure ()

prop_labeling_quirks_and_errors :: Property
prop_labeling_quirks_and_errors = unit $ do
  forM_
    [ "X in 1..3, label [X | Tail]?",
      "X in 1..3, label [wrapper X, ignored]?",
      "X in 1..3, labeling [min X] [X | Tail]?",
      "X in 1..3, labeling [min X] [wrapper X]?",
      "X in 1..3, labeling [min X] [X, 0]?",
      "label [X, Y]?",
      "labeling [min X] [X, Y]?",
      "X in 1..3, labeling [min Y] [X]?",
      "X in 1..3, labeling [min bad] [X]?",
      "X in 1..3, labeling [wrong X] [X]?",
      "[X, Y] in 1..3, Cost #= 0, labeling [min Cost] [X, Y]?",
      "X in 1..3, all_different [X | Tail]?",
      "X in 1..3, reify Unknown B?",
      "X in 1..3, reify (X #< 2) bad?",
      "X in 1..3, X in bad?"
    ] $ \source -> compareText emptyProgram source >> pure ()

prop_large_integer_and_holey_domain :: Property
prop_large_integer_and_holey_domain = unit $ do
  let huge = 10 ^ (80 :: Int)
      x = Var 0; y = Var 1; truth = Var 2
      query = Query
        [ domain x huge (huge + 3), app "fd_ne" [x, IntLit (huge + 1)],
          app "int_eq" [y, app "minus" [x, IntLit huge]],
          app "reify" [app "fd_gt" [y, IntLit 1], truth],
          app "label" [list [x, y, truth]]
        ] [("X", 0), ("Y", 1), ("B", 2)] 3
  items <- compareQuery emptyProgram query
  noIssues items
  sort (map (values [0, 1, 2]) (found items)) ===
    [map IntLit [huge, 0, 0], map IntLit [huge + 2, 2, 1], map IntLit [huge + 3, 3, 1]]

must :: ST s (Either Heap.HeapError a) -> ST s a
must action = action >>= either (error . show) pure

data Operation
  = Restrict VarId Integer Integer
  | Relate Rel Term Term
  | Unify Term Term
  | Distinct [Term]
  | Reified Rel Term Term Term
  deriving (Show)

applyPure :: Operation -> Store -> Either SolveError (Maybe Store)
applyPure operation store = case operation of
  Restrict variable lo hi -> addDomain (Var variable) (Fin lo) (Fin hi) store
  Relate relation left right -> addRelation relation left right store
  Unify left right -> storeUnify store left right
  Distinct terms -> addAllDifferent terms store
  Reified relation left right truth -> addReified relation left right truth store

applyNative :: Heap.Heap s -> Bridge.Bindings -> Store -> Operation -> [Heap.Address]
  -> ST s (Either Heap.HeapError (Either SolveError (Maybe (Bridge.Bindings, Store))))
applyNative heap bindings store operation addresses = case operation of
  Unify _ _ -> case addresses of
    [a, b] -> Native.unify heap bindings store a b
    _ -> error "import changed the number of roots"
  _ -> Native.apply heap bindings store (applyPure operation)

genOperation :: Gen Operation
genOperation = Gen.choice
  [ Restrict <$> variable <*> Gen.integral (Range.linear (-3) 1)
      <*> Gen.integral (Range.linear 1 4),
    Relate <$> Gen.element [RelEq, RelNe, RelLe] <*> term <*> term,
    Unify <$> term <*> term,
    pure (Unify (app "pair" [Var 0, Var 1]) (app "pair" [IntLit 2, Atom "bad"])),
    pure (Distinct [Var 0, Var 1, Var 2]),
    Reified <$> Gen.element [RelEq, RelNe, RelLe] <*> term <*> term <*> pure (Var 3)
  ]
  where
    variable = Gen.int (Range.linear 0 3)
    term = Gen.choice [Var <$> variable, IntLit <$> Gen.integral (Range.linear (-3) 4)]

-- Collect immutable observations inside ST, then assert outside it. For each
-- rejected transaction heap content AND allocation/trail frontiers must match.
prop_generated_backend_transactions :: Property
prop_generated_backend_transactions = withTests 300 . property $ do
  operations <- forAll (Gen.list (Range.linear 1 18) genOperation)
  let observations = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0 .. 3])
        let run _ _ [] = pure []
            run current store (operation : rest) = do
              let terms = case operation of Unify a b -> [a, b]; _ -> []
              (prepared, addresses) <- must (Bridge.importTerms heap current terms)
              (_, roots) <- must (Bridge.importTerms heap prepared (map Var [0 .. 3]))
              before <- must (Bridge.exportTerms heap prepared roots)
              beforeHeap <- Heap.heapSize heap
              beforeTrail <- Heap.trailSize heap
              actual <- applyNative heap prepared store operation addresses
              let expected = applyPure operation store
                  (nextBindings, nextStore) = case actual of
                    Right (Right (Just pair)) -> pair
                    _ -> (prepared, store)
              after <- must (Bridge.exportTerms heap nextBindings roots)
              afterHeap <- Heap.heapSize heap
              afterTrail <- Heap.trailSize heap
              more <- run nextBindings nextStore rest
              pure ((fmap (fmap (fmap snd)) actual, expected, before, after,
                (beforeHeap, beforeTrail), (afterHeap, afterTrail), nextStore) : more)
        run bindings emptyStore operations
  forM_ observations $ \(actual, expected, before, after, beforeSizes, afterSizes, nextStore) -> do
    actual === Right expected
    case expected of
      Right (Just _) -> after === map (deepWalk (stSubst nextStore) . Var) [0 .. 3]
      _ -> do
        after === before
        afterSizes === beforeSizes

prop_backend_logical_alias_order_and_wakeup :: Property
prop_backend_logical_alias_order_and_wakeup = unit $ do
  let result = runST $ do
        heap <- Heap.newHeap
        highBindings <- must (Bridge.newBindings heap [100])
        posted <- must (Native.apply heap highBindings emptyStore (addDomain (Var 100) (Fin 1) (Fin 4)))
        case posted of
          Right (Just (withHigh, store)) -> do
            (withLow, addresses) <- must (Bridge.importTerms heap withHigh [Var 2, Var 100])
            case addresses of
              [low, high] -> do
                aliased <- must (Native.unify heap withLow store low high)
                case aliased of
                  Right (Just (finalBindings, finalStore)) -> do
                    roots <- must (Bridge.exportTerms heap finalBindings [low, high])
                    pure (roots, finalStore)
                  _ -> error "alias unexpectedly failed"
              _ -> error "import changed the number of roots"
          _ -> error "domain unexpectedly failed"
      expected = addDomain (Var 100) (Fin 1) (Fin 4) emptyStore
        >>= maybe (Right Nothing) (\store -> storeUnify store (Var 2) (Var 100))
  fst result === [Var 2, Var 2]
  Right (Just (snd result)) === expected
  domainOf (snd result) 2 === Just (Domain (Fin 1) (Fin 4) mempty)

prop_backend_checkpoint_and_frozen_store :: Property
prop_backend_checkpoint_and_frozen_store = unit $ do
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0 .. 3])
        initial <- must (Native.apply heap bindings emptyStore $ \store ->
          addDomains [Var 0, Var 1] (Fin 1) (Fin 4) store
            >>= maybe (Right Nothing) (addRelation RelNe (Var 0) (Var 1)))
        case initial of
          Right (Just (initialBindings, postedStore)) -> do
            -- Public Store callers may retain pending and dirty work. A
            -- checkpoint must retain it verbatim, including sparse future
            -- constraint numbering, rather than reconstruct residual terms.
            let initialStore = postedStore
                  { stPending = IM.keysSet (stConstraintMap postedStore),
                    stDirtyVars = IS.fromList [0, 1],
                    stNextConstraint = stNextConstraint postedStore + 7
                  }
            (_, roots) <- must (Bridge.importTerms heap initialBindings (map Var [0 .. 3]))
            before <- must (Bridge.exportTerms heap initialBindings roots)
            mark <- Heap.checkpoint heap
            frozen <- Heap.freezeHeap heap
            let branch value = do
                  child <- Heap.thawHeap frozen
                  bound <- must (Native.bindInteger child initialBindings initialStore 0 value)
                  case bound of
                    Right (Just (childBindings, childStore)) -> do
                      terms <- must (Bridge.exportTerms child childBindings roots)
                      pure (terms, childStore)
                    _ -> error "bounded integer unexpectedly failed"
            first <- branch 1
            second <- branch 3
            repeated <- branch 1
            live <- must (Native.bindInteger heap initialBindings initialStore 0 2)
            case live of
              Right (Just _) -> pure ()
              _ -> error "live integer unexpectedly failed"
            _ <- must (Heap.rollback heap mark)
            after <- must (Bridge.exportTerms heap initialBindings roots)
            pure (before, after, initialStore, first, second, repeated)
          _ -> error "initial domains unexpectedly failed"
  case result of
    (before, after, initialStore, first, second, repeated) -> do
      after === before
      first === repeated
      fst first === [IntLit 1, Var 1, Var 2, Var 3]
      fst second === [IntLit 3, Var 1, Var 2, Var 3]
      Right (Just (snd first)) === storeBind initialStore 0 1
      Right (Just (snd second)) === storeBind initialStore 0 3

prop_backend_unchanged_nan_and_singletons :: Property
prop_backend_unchanged_nan_and_singletons = unit $ do
  let nan = 0 / 0
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0, 1])
        (imported, addresses) <- must (Bridge.importTerms heap bindings [Var 0, Var 1, FloatLit nan])
        case addresses of
          [root, integerRoot, scalar] -> do
            bound <- must (Native.unify heap imported emptyStore root scalar)
            case bound of
              Right (Just (withNaN, store)) -> do
                narrowed <- must (Native.apply heap withNaN store (addDomain (Var 1) (Fin 2) (Fin 2)))
                case narrowed of
                  Right (Just (finalBindings, finalStore)) -> do
                    before <- must (Bridge.exportTerms heap finalBindings [root, integerRoot])
                    beforeSize <- (,) <$> Heap.heapSize heap <*> Heap.trailSize heap
                    rejected <- must (Native.unify heap finalBindings finalStore root root)
                    after <- must (Bridge.exportTerms heap finalBindings [root, integerRoot])
                    afterSize <- (,) <$> Heap.heapSize heap <*> Heap.trailSize heap
                    let bits terms = case terms of
                          [FloatLit value, IntLit integer] -> (castDoubleToWord64 value, integer)
                          _ -> error "NaN or singleton changed its scalar type"
                    pure (bits before, bits after, beforeSize, afterSize,
                      case rejected of Right Nothing -> True; _ -> False)
                  _ -> error "unrelated singleton domain unexpectedly failed"
              _ -> error "binding a free variable to NaN unexpectedly failed"
          _ -> error "import changed the number of roots"
  case result of
    (before, after, beforeSize, afterSize, rejected) -> do
      before === (castDoubleToWord64 nan, 2)
      after === before
      afterSize === beforeSize
      assert rejected

drain :: Machine.Checkpoint -> Either Heap.HeapError Reference.Search
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure []
    Machine.Yield item next -> (item :) <$> drain next

prop_native_interleaved_label_resumes :: Property
prop_native_interleaved_label_resumes = unit $ do
  query <- evalEither (parseQuery "[X, Y] in 1..4, X #!= 2, reify (X #< Y) B, label [X, Y, B]?")
  initial <- evalEither (Machine.start emptyProgram query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Yield item next -> do
      one <- evalEither (drain next)
      parent <- evalEither (drain initial)
      two <- evalEither (drain next)
      observe query one === observe query two
      observe query parent === observe query (item : one)
      observe query parent === observe query (Reference.solveQuery emptyProgram query)
    Machine.Finished -> failure

prop_noncanonical_start_goals_identity :: Property
prop_noncanonical_start_goals_identity = unit $ do
  posted <- evalEither (addDomain (Var 1) (Fin 1) (Fin 3) emptyStore)
  store <- maybe failure pure posted
  let original = store {stSubst = IM.singleton 0 (Var 1)}
      state = (Reference.initialState 3) {Reference.ssStore = original}
      environment = Reference.mkEnv emptyProgram
      compareGoals goals = do
        let query = Query goals [("X", 0), ("Y", 1), ("List", 2)] 3
        observe query (Machine.solveGoals environment 100 state goals) ===
          observe query (Reference.solveGoals environment 100 state goals)
  forM_
    [ [],
      [app "unify" [Var 0, IntLit 2]],
      [app "unify" [Var 1, Atom "bad"]],
      [domain (Var 0) 1 2, app "label" [list [Var 1]]],
      [app "once" [app "unify" [Var 0, IntLit 2]]],
      [app "call" [app "unify" [Var 0, IntLit 2]]],
      [app "not" [app "unify" [Var 0, IntLit 9]], app "label" [list [Var 1]]],
      [app "findall" [Var 0, app "label" [list [Var 1]], Var 2]],
      [app "labeling" [list [app "min" [Var 0]], list [Var 0, Var 1]]],
      [app "str_length" [StrLit "ab", Var 0]]
    ] compareGoals

prop_backend_sync_preserves_input_alias_identity :: Property
prop_backend_sync_preserves_input_alias_identity = unit $ do
  posted <- evalEither (addDomain (Var 1) (Fin 1) (Fin 3) emptyStore)
  store <- maybe failure pure posted
  let original = store {stSubst = IM.singleton 0 (Var 1)}
      state = (Reference.initialState 2) {Reference.ssStore = original}
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0, 1])
        (_, roots) <- must (Bridge.importTerms heap bindings [Var 0, Var 1])
        mark <- Heap.checkpoint heap
        synchronized <- must (Bridge.syncState heap bindings state)
        frozen <- Heap.freezeHeap heap
        case roots of
          [left, right] -> do
            leftRepresentative <- must (Heap.dereference heap left)
            rightRepresentative <- must (Heap.dereference heap right)
            let child value = do
                  resumed <- Heap.thawHeap frozen
                  bound <- must (Native.bindInteger resumed synchronized original 0 value)
                  case bound of
                    Right (Just (finalBindings, finalStore)) -> do
                      terms <- must (Bridge.exportTerms resumed finalBindings roots)
                      pure (terms, finalStore)
                    _ -> error "valid noncanonical alias binding unexpectedly failed"
            first <- child 1
            second <- child 3
            _ <- must (Heap.rollback heap mark)
            restored <- must (Bridge.exportTerms heap bindings roots)
            pure (leftRepresentative == right, rightRepresentative == right, first, second, restored)
          _ -> error "import changed the number of roots"
  case result of
    (leftIdentity, rightIdentity, first, second, restored) -> do
      assert leftIdentity
      assert rightIdentity
      fst first === [IntLit 1, IntLit 1]
      fst second === [IntLit 3, IntLit 3]
      Right (Just (snd first)) === storeBind original 0 1
      Right (Just (snd second)) === storeBind original 0 3
      restored === [Var 0, Var 1]

machineCLPGroup :: Group
machineCLPGroup = Group "machine CLP"
  [ ("bounded_reification_abs_and_distinct", prop_bounded_reification_abs_and_distinct),
    ("bounded_branch_and_bound_model", prop_bounded_branch_and_bound_model),
    ("aliases_domains_and_clause_retries", prop_aliases_domains_and_clause_retries),
    ("nested_subsearch_complete_store", prop_nested_subsearch_complete_store),
    ("labeling_quirks_and_errors", prop_labeling_quirks_and_errors),
    ("large_integer_and_holey_domain", prop_large_integer_and_holey_domain),
    ("generated_backend_transactions", prop_generated_backend_transactions),
    ("backend_logical_alias_order_and_wakeup", prop_backend_logical_alias_order_and_wakeup),
    ("backend_checkpoint_and_frozen_store", prop_backend_checkpoint_and_frozen_store),
    ("backend_unchanged_nan_and_singletons", prop_backend_unchanged_nan_and_singletons),
    ("native_interleaved_label_resumes", prop_native_interleaved_label_resumes),
    ("noncanonical_start_goals_identity", prop_noncanonical_start_goals_identity),
    ("backend_sync_preserves_input_alias_identity", prop_backend_sync_preserves_input_alias_identity)
  ]
