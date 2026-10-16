{-# LANGUAGE OverloadedStrings #-}

-- The machine heap is still an execution foundation. Its contract is tested
-- against the current pure unifier before either representation drives search.
-- Observe every root together: comparing separately would conceal lost aliases.
module MachineHeapTest (machineHeapGroup) where

import Control.Monad (forM, forM_)
import Control.Monad.ST (ST, runST)
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax
import qualified Infera.Unify as Reference

-- Double's Eq makes NaN unequal to itself and erases the sign of zero. Export
-- checks instead compare its bits, so they can detect changes in scalar data.
data Observed
  = OAtom String
  | OVar VarId
  | OInt Integer
  | OFloat Word64
  | OChar Char
  | OString String
  | OCompound String [Observed]
  deriving (Eq, Show)

observe :: Term -> Observed
observe term = case term of
  Atom value -> OAtom value
  Var value -> OVar value
  IntLit value -> OInt value
  FloatLit value -> OFloat (castDoubleToWord64 value)
  CharLit value -> OChar value
  StrLit value -> OString value
  Compound name arguments -> OCompound name (map observe arguments)

referenceRoots :: Reference.Subst -> [Term] -> [Observed]
referenceRoots subst roots = case fst (Reference.canonicalize subst (Compound "$roots" roots)) of
  Compound _ terms -> map observe terms
  _ -> error "canonicalizing a compound changed its constructor"

must :: Show err => ST s (Either err a) -> ST s a
must action = action >>= either (error . show) pure

importRoots :: Heap.Heap s -> [Term] -> ST s [Heap.Address]
importRoots heap = go Heap.emptyEnvironment
  where
    go _ [] = pure []
    go environment (term : rest) = do
      (address, environment') <- must (Heap.importWithEnvironment heap environment term)
      (address :) <$> go environment' rest

exportRoots :: Heap.Heap s -> [Heap.Address] -> ST s [Observed]
exportRoots heap roots = map observe <$> must (Heap.exportTerms heap roots)

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["nil", "a", "b", "\955", "\38634"],
    IntLit <$> Gen.choice
      [ Gen.integral (Range.linear (-4) 4),
        Gen.element [negate (2 ^ (130 :: Int)), 2 ^ (130 :: Int) + 37]
      ],
    FloatLit <$> Gen.element [-1 / 0, -2.5, -1, -0.0, 0, 1, 2.5, 1 / 0, 0 / 0],
    CharLit <$> Gen.element ['a', '\n', '\0', '\955', '\128578'],
    StrLit <$> Gen.element ["", "a", "line\nnext", "\955\38634\128578", "\0"]
  ]

genTerm :: Int -> Gen Term
genTerm depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency
      [ (5, leaf),
        (3, Compound <$> Gen.element ["pair", "node", "\955", "cons", "zero"]
          <*> Gen.list (Range.linear 0 3) (genTerm (depth - 1)))
      ]
  where
    leaf = Gen.frequency [(3, Var <$> Gen.int (Range.linear 0 5)), (4, genScalar)]

type Pair = (Int, Int)

genPairs :: Int -> Gen [Pair]
genPairs count = Gen.list (Range.linear 0 15) $
  (,) <$> Gen.int (Range.linear 0 (count - 1)) <*> Gen.int (Range.linear 0 (count - 1))

referenceUnify :: [Term] -> Reference.Subst -> Pair -> (Bool, Reference.Subst)
referenceUnify roots subst (left, right) =
  case Reference.unifyPlain subst (roots !! left) (roots !! right) of
    Nothing -> (False, subst)
    Just subst' -> (True, subst')

referenceSteps :: [Term] -> Reference.Subst -> [Pair] -> (Reference.Subst, [(Bool, [Observed])])
referenceSteps roots = go
  where
    go subst [] = (subst, [])
    go subst (pair : rest) =
      let (accepted, subst') = referenceUnify roots subst pair
          (final, observations) = go subst' rest
       in (final, (accepted, referenceRoots subst' roots) : observations)

heapSteps :: Heap.Heap s -> [Heap.Address] -> [Pair] -> ST s [(Bool, [Observed])]
heapSteps heap roots = mapM $ \(left, right) -> do
  accepted <- must (Heap.unify heap (roots !! left) (roots !! right))
  terms <- exportRoots heap roots
  pure (accepted, terms)

prop_term_round_trip :: Property
prop_term_round_trip = withTests 300 $ property $ do
  terms <- forAll (Gen.list (Range.linear 0 16) (genTerm 3))
  let (first, second) = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        firstExport <- exportRoots heap roots
        secondExport <- exportRoots heap roots
        pure (firstExport, secondExport)
  first === referenceRoots Reference.emptySubst terms
  second === first

prop_unification_sequence :: Property
prop_unification_sequence = withTests 300 $ property $ do
  extras <- forAll (Gen.list (Range.linear 1 12) (genTerm 3))
  let terms = map Var [0 .. 5] ++ extras
  pairs <- forAll (genPairs (length terms))
  let actual = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        heapSteps heap roots pairs
      (_, expected) = referenceSteps terms Reference.emptySubst pairs
  actual === expected

data Script = Bind Pair | Scope [Script]
  deriving Show

genScript :: Int -> Int -> Gen [Script]
genScript count depth = Gen.list (Range.linear 0 8) $ Gen.frequency $
  [(5, Bind <$> ((,) <$> index <*> index))]
  ++ [(2, Scope <$> genScript count (depth - 1)) | depth > 0]
  where
    index = Gen.int (Range.linear 0 (count - 1))

type Event = (Maybe Bool, [Observed])

referenceScript :: [Term] -> Reference.Subst -> [Script] -> (Reference.Subst, [Event])
referenceScript roots = go
  where
    go subst [] = (subst, [])
    go subst (Bind pair : rest) =
      let (accepted, subst') = referenceUnify roots subst pair
          (final, observations) = go subst' rest
       in (final, (Just accepted, referenceRoots subst' roots) : observations)
    go subst (Scope inner : rest) =
      let (_, innerObservations) = go subst inner
          (final, restObservations) = go subst rest
       in (final, innerObservations ++ (Nothing, referenceRoots subst roots) : restObservations)

heapScript :: Heap.Heap s -> [Heap.Address] -> [Script] -> ST s [Event]
heapScript heap roots = go
  where
    go [] = pure []
    go (Bind (left, right) : rest) = do
      accepted <- must (Heap.unify heap (roots !! left) (roots !! right))
      terms <- exportRoots heap roots
      ((Just accepted, terms) :) <$> go rest
    go (Scope inner : rest) = do
      mark <- Heap.checkpoint heap
      observations <- go inner
      must (Heap.rollback heap mark)
      restored <- exportRoots heap roots
      remaining <- go rest
      pure (observations ++ (Nothing, restored) : remaining)

prop_nested_rollback :: Property
prop_nested_rollback = withTests 300 $ property $ do
  extras <- forAll (Gen.list (Range.linear 1 10) (genTerm 2))
  let terms = map Var [0 .. 5] ++ extras
  script <- forAll (genScript (length terms) 2)
  let actual = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        heapScript heap roots script
      (_, expected) = referenceScript terms Reference.emptySubst script
  actual === expected

prop_frozen_branches :: Property
prop_frozen_branches = withTests 300 $ property $ do
  extras <- forAll (Gen.list (Range.linear 1 10) (genTerm 2))
  let terms = map Var [0 .. 5] ++ extras
  prefix <- forAll (genPairs (length terms))
  firstBranch <- forAll (genPairs (length terms))
  secondBranch <- forAll (genPairs (length terms))
  let (prefixSubst, prefixExpected) = referenceSteps terms Reference.emptySubst prefix
      (_, firstExpected) = referenceSteps terms prefixSubst firstBranch
      (_, secondExpected) = referenceSteps terms prefixSubst secondBranch
      retainedExpected = referenceRoots prefixSubst terms
      actual = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        prefixActual <- heapSteps heap roots prefix
        mark <- Heap.checkpoint heap
        retained <- must (Heap.exportTerms heap roots)
        frozen <- Heap.freezeHeap heap
        first <- Heap.thawHeap frozen
        firstActual <- heapSteps first roots firstBranch
        firstFrozen <- Heap.freezeHeap first
        second <- Heap.thawHeap frozen
        secondActual <- heapSteps second roots secondBranch
        -- Resume the first branch after the second one has made writes.
        resumed <- Heap.thawHeap firstFrozen
        resumedTerms <- exportRoots resumed roots
        must (Heap.rollback resumed mark)
        resumedRestored <- exportRoots resumed roots
        must (Heap.rollback first mark)
        firstRestored <- exportRoots first roots
        parentTerms <- exportRoots heap roots
        repeated <- Heap.thawHeap frozen
        repeatedActual <- heapSteps repeated roots firstBranch
        pure (prefixActual, firstActual, secondActual, repeatedActual,
              resumedTerms, resumedRestored, firstRestored, parentTerms, map observe retained)
      firstFinal = case reverse firstExpected of
        (_, observed) : _ -> observed
        [] -> retainedExpected
  actual === (prefixExpected, firstExpected, secondExpected, firstExpected,
              firstFinal, retainedExpected, retainedExpected, retainedExpected, retainedExpected)

prop_late_allocation_rollback :: Property
prop_late_allocation_rollback = withTests 300 $ property $ do
  term <- forAll (genTerm 3)
  let initial = [Var 0, Var 1]
      terms = initial ++ [term]
      (accepted, subst) = referenceUnify terms Reference.emptySubst (0, 2)
      expectedBound = take 2 (referenceRoots subst terms)
      expectedRestored = referenceRoots Reference.emptySubst initial
      expectedFresh = referenceRoots Reference.emptySubst
        (initial ++ [Reference.renameTerm 100 term])
      result = runST $ do
        heap <- Heap.newHeap
        (x, environment) <- must (Heap.importWithEnvironment heap Heap.emptyEnvironment (Var 0))
        (y, shared) <- must (Heap.importWithEnvironment heap environment (Var 1))
        mark <- Heap.checkpoint heap
        (later, _) <- must (Heap.importWithEnvironment heap shared term)
        actualAccepted <- must (Heap.unify heap x later)
        bound <- exportRoots heap [x, y]
        frozen <- Heap.freezeHeap heap
        must (Heap.rollback heap mark)
        restored <- exportRoots heap [x, y]
        fresh <- must (Heap.importTerm heap term)
        reallocated <- exportRoots heap [x, y, fresh]
        resumed <- Heap.thawHeap frozen
        resumedBound <- exportRoots resumed [x, y]
        must (Heap.rollback resumed mark)
        resumedRestored <- exportRoots resumed [x, y]
        pure (actualAccepted, bound, restored, reallocated, resumedBound, resumedRestored)
  result === (accepted, expectedBound, expectedRestored, expectedFresh, expectedBound, expectedRestored)

prop_import_scope :: Property
prop_import_scope = withTests 1 $ property $ do
  let term = Compound "box" [Var 47, Var 47]
      independentExpected = [OCompound "box" [OInt 7, OInt 7],
                             OCompound "box" [OVar 0, OVar 0]]
      sharedExpected = replicate 2 (OCompound "box" [OInt 7, OInt 7])
      (independent, shared) = runST $ do
        heap <- Heap.newHeap
        first <- must (Heap.importTerm heap term)
        second <- must (Heap.importTerm heap term)
        bound <- must (Heap.importTerm heap (Compound "box" [IntLit 7, IntLit 7]))
        _ <- must (Heap.unify heap first bound)
        independentExport <- exportRoots heap [first, second]
        other <- Heap.newHeap
        (a, environment) <- must (Heap.importWithEnvironment other Heap.emptyEnvironment term)
        (b, _) <- must (Heap.importWithEnvironment other environment term)
        value <- must (Heap.importTerm other (Compound "box" [IntLit 7, IntLit 7]))
        _ <- must (Heap.unify other a value)
        sharedExport <- exportRoots other [a, b]
        pure (independentExport, sharedExport)
  independent === independentExpected
  shared === sharedExpected

prop_failure_is_atomic :: Property
prop_failure_is_atomic = withTests 1 $ property $ do
  let terms = [Var 0, Var 1, Compound "pair" [Var 0, Atom "a"],
               Compound "pair" [IntLit 1, Atom "b"], Compound "box" [Var 0]]
      result = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        mark <- Heap.checkpoint heap
        size <- Heap.heapSize heap
        trail <- Heap.trailSize heap
        failed <- must (Heap.unify heap (roots !! 2) (roots !! 3))
        afterFailure <- exportRoots heap roots
        sizeAfter <- Heap.heapSize heap
        trailAfter <- Heap.trailSize heap
        aliased <- must (Heap.unify heap (roots !! 0) (roots !! 1))
        occurred <- must (Heap.unify heap (roots !! 1) (roots !! 4))
        afterOccurs <- exportRoots heap roots
        must (Heap.rollback heap mark)
        restored <- exportRoots heap roots
        pure (failed, afterFailure, sizeAfter == size, trailAfter == trail,
              aliased, occurred, afterOccurs, restored)
      initial = referenceRoots Reference.emptySubst terms
      aliasSubst = maybe (error "two distinct free variables must unify") id
        (Reference.unifyPlain Reference.emptySubst (Var 0) (Var 1))
  result === (False, initial, True, True, True, False, referenceRoots aliasSubst terms, initial)

prop_scalar_identity :: Property
prop_scalar_identity = withTests 1 $ property $ do
  let scalars = [Atom "a", Atom "\955", StrLit "a", StrLit "\955\38634", CharLit 'a',
                 CharLit '\128578', IntLit 0, IntLit 1, IntLit (2 ^ (130 :: Int)),
                 FloatLit (-0.0), FloatLit 0, FloatLit 1, FloatLit (1 / 0), FloatLit (0 / 0)]
      nanCompound = Compound "nested" [Compound "box" [FloatLit (0 / 0)]]
  forM_ [(a, b) | a <- scalars, b <- scalars] $ \(left, right) -> do
    annotateShow (left, right)
    let actual = runST $ do
          heap <- Heap.newHeap
          roots <- importRoots heap [left, right]
          accepted <- must (Heap.unify heap (roots !! 0) (roots !! 1))
          output <- exportRoots heap roots
          pure (accepted, output)
        expected = referenceSteps [left, right] Reference.emptySubst [(0, 1)]
    [actual] === snd expected
  -- A pointer-equality shortcut must not make NaN-containing terms reflexive:
  -- the existing term unifier deliberately follows Double's equality here.
  forM_ (scalars ++ [nanCompound, Compound "pair" [Var 0, FloatLit (0 / 0)]]) $ \term -> do
    annotateShow term
    let actual = runST $ do
          heap <- Heap.newHeap
          root <- must (Heap.importTerm heap term)
          accepted <- must (Heap.unify heap root root)
          output <- exportRoots heap [root]
          pure (accepted, output)
    [actual] === snd (referenceSteps [term] Reference.emptySubst [(0, 0)])
  -- The same rule applies after dereferencing a variable that was already
  -- bound to NaN. Rejecting self-unification must retain its earlier binding.
  let nan = FloatLit (0 / 0)
      boundNaN = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap [Var 0, nan]
        accepted <- must (Heap.unify heap (roots !! 0) (roots !! 1))
        size <- Heap.heapSize heap
        trail <- Heap.trailSize heap
        self <- must (Heap.unify heap (roots !! 0) (roots !! 0))
        retained <- exportRoots heap roots
        sizeAfter <- Heap.heapSize heap
        trailAfter <- Heap.trailSize heap
        pure (accepted, self, retained, sizeAfter == size, trailAfter == trail)
  boundNaN === (True, False, replicate 2 (observe nan), True, True)

prop_discarded_addresses :: Property
prop_discarded_addresses = withTests 1 $ property $ do
  let result = runST $ do
        heap <- Heap.newHeap
        old <- must (Heap.newVariable heap)
        mark <- Heap.checkpoint heap
        stale <- must (Heap.newVariable heap)
        must (Heap.rollback heap mark)
        replacement <- must (Heap.newVariable heap)
        staleExport <- Heap.exportTerm heap stale
        staleUnify <- Heap.unify heap stale replacement
        staleSelf <- Heap.unify heap stale stale
        surviving <- exportRoots heap [old, replacement]
        pure (staleExport == Left (Heap.InvalidAddress stale),
              staleUnify == Left (Heap.InvalidAddress stale),
              staleSelf == Left (Heap.InvalidAddress stale), surviving)
  result === (True, True, True, [OVar 0, OVar 1])
  -- Environments are handles too: even an import that does not mention the
  -- discarded source variable must reject the stale environment atomically.
  let environmentResult = runST $ do
        heap <- Heap.newHeap
        surviving <- must (Heap.newVariable heap)
        mark <- Heap.checkpoint heap
        (discarded, environment) <- must
          (Heap.importWithEnvironment heap Heap.emptyEnvironment (Var 47))
        must (Heap.rollback heap mark)
        replacement <- must (Heap.newVariable heap)
        size <- Heap.heapSize heap
        trail <- Heap.trailSize heap
        imported <- Heap.importWithEnvironment heap environment (Atom "unrelated")
        let invalid = case imported of
              Left err -> err == Heap.InvalidAddress discarded
              Right _ -> False
        retained <- exportRoots heap [surviving, replacement]
        sizeAfter <- Heap.heapSize heap
        trailAfter <- Heap.trailSize heap
        pure (invalid, retained, sizeAfter == size, trailAfter == trail)
  environmentResult === (True, [OVar 0, OVar 1], True, True)

prop_checkpoint_lineage :: Property
prop_checkpoint_lineage = withTests 1 $ property $ do
  let result = runST $ do
        heap <- Heap.newHeap
        variable <- must (Heap.newVariable heap)
        first <- Heap.checkpoint heap
        _ <- must (Heap.newVariable heap)
        discarded <- Heap.checkpoint heap
        _ <- must (Heap.newVariable heap)
        must (Heap.rollback heap first)
        _ <- must (Heap.newVariable heap)
        invalid <- Heap.rollback heap discarded
        must (Heap.rollback heap first)
        value <- must (Heap.importTerm heap (IntLit 3))
        accepted <- must (Heap.unify heap variable value)
        must (Heap.rollback heap first)
        firstRestore <- exportRoots heap [variable]
        must (Heap.rollback heap first)
        secondRestore <- exportRoots heap [variable]
        pure (invalid, accepted, firstRestore, secondRestore)
  result === (Left Heap.InvalidCheckpoint, True, [OVar 0], [OVar 0])
  -- A discarded future can differ only in bindings, with no heap allocation.
  -- Reusing the same trail length must not make its checkpoint valid again.
  let trailResult = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap [Var 0, Var 1, IntLit 1, IntLit 2]
        start <- Heap.checkpoint heap
        _ <- must (Heap.unify heap (roots !! 0) (roots !! 2))
        discarded <- Heap.checkpoint heap
        must (Heap.rollback heap start)
        _ <- must (Heap.unify heap (roots !! 1) (roots !! 3))
        invalid <- Heap.rollback heap discarded
        retained <- exportRoots heap roots
        pure (invalid, retained)
  trailResult === (Left Heap.InvalidCheckpoint, [OVar 0, OInt 2, OInt 1, OInt 2])

prop_frozen_trail :: Property
prop_frozen_trail = withTests 1 $ property $ do
  let result = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap [Var 0, Var 1, IntLit 4, IntLit 9]
        initial <- Heap.checkpoint heap
        _ <- must (Heap.unify heap (roots !! 0) (roots !! 2))
        middle <- Heap.checkpoint heap
        frozen <- Heap.freezeHeap heap
        left <- Heap.thawHeap frozen
        _ <- must (Heap.unify left (roots !! 1) (roots !! 3))
        frozenLeft <- Heap.freezeHeap left
        must (Heap.rollback left middle)
        leftRestored <- exportRoots left roots
        right <- Heap.thawHeap frozen
        must (Heap.rollback right initial)
        rightRestored <- exportRoots right roots
        resumed <- Heap.thawHeap frozenLeft
        resumedBefore <- exportRoots resumed roots
        must (Heap.rollback resumed initial)
        resumedRestored <- exportRoots resumed roots
        parent <- exportRoots heap roots
        pure (leftRestored, rightRestored, resumedBefore, resumedRestored, parent)
      initialTerms = [OVar 0, OVar 1, OInt 4, OInt 9]
      middleTerms = [OInt 4, OVar 0, OInt 4, OInt 9]
      finalTerms = [OInt 4, OInt 9, OInt 4, OInt 9]
  result === (middleTerms, initialTerms, finalTerms, initialTerms, middleTerms)

prop_page_growth_and_forks :: Property
prop_page_growth_and_forks = withTests 1 $ property $ do
  let count = 400
      positions = [0, 1, 63, 127, 128, 129, 255, 256, 399]
      terms = map Var [0 .. count - 1]
      result = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        initial <- Heap.checkpoint heap
        frozen <- Heap.freezeHeap heap
        branches <- forM [11, 22] $ \value -> do
          child <- Heap.thawHeap frozen
          scalar <- must (Heap.importTerm child (IntLit value))
          forM_ positions $ \position -> must (Heap.unify child (roots !! position) scalar)
          sparse <- Heap.freezeHeap child
          -- Grow the trail past a page as well as the heap, after the first
          -- snapshot has shared the partially bound pages.
          forM_ [index | index <- [0 .. count - 1], index `notElem` positions] $ \position ->
            must (Heap.unify child (roots !! position) scalar)
          dense <- Heap.freezeHeap child
          must (Heap.rollback child initial)
          restored <- exportRoots child roots
          pure (sparse, dense, restored)
        -- Both snapshots are read only after writes and rollbacks in the other
        -- branch; separate offsets within a page matter as well as page edges.
        resumed <- forM branches $ \(sparse, dense, restored) -> do
          sparseChild <- Heap.thawHeap sparse
          sparseTerms <- exportRoots sparseChild roots
          denseChild <- Heap.thawHeap dense
          denseTerms <- exportRoots denseChild roots
          must (Heap.rollback denseChild initial)
          denseRestored <- exportRoots denseChild roots
          pure (sparseTerms, denseTerms, denseRestored, restored)
        parent <- exportRoots heap roots
        pure (resumed, parent)
      expected value = referenceRoots Reference.emptySubst
        [if index `elem` positions then IntLit value else Var index | index <- [0 .. count - 1]]
      initialTerms = referenceRoots Reference.emptySubst terms
      expectedBranch value = (expected value, replicate count (OInt value), initialTerms, initialTerms)
  result === ([expectedBranch 11, expectedBranch 22], initialTerms)

machineHeapGroup :: Group
machineHeapGroup = Group "machine heap"
  [ ("term_round_trip", prop_term_round_trip),
    ("unification_sequence", prop_unification_sequence),
    ("nested_rollback", prop_nested_rollback),
    ("frozen_branches", prop_frozen_branches),
    ("late_allocation_rollback", prop_late_allocation_rollback),
    ("import_scope", prop_import_scope),
    ("failure_is_atomic", prop_failure_is_atomic),
    ("scalar_identity", prop_scalar_identity),
    ("discarded_addresses", prop_discarded_addresses),
    ("checkpoint_lineage", prop_checkpoint_lineage),
    ("frozen_trail", prop_frozen_trail),
    ("page_growth_and_forks", prop_page_growth_and_forks)
  ]
