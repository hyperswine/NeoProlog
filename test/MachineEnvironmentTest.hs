{-# LANGUAGE OverloadedStrings #-}

-- Activation environments validate a complete allocation prefix through its
-- newest root. These models vary source-ID order independently of heap order
-- and exercise bindings, rollbacks, replacement heaps and paired snapshots.
module MachineEnvironmentTest (machineEnvironmentGroup) where

import Control.Monad (forM, forM_)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax
import qualified Infera.Unify as Reference

must :: Show err => ST s (Either err a) -> ST s a
must action = action >>= either (error . show) pure

importMany :: Heap.Heap s -> Heap.Environment -> [VarId]
  -> ST s ([Heap.Address], Heap.Environment)
importMany _ environment [] = pure ([], environment)
importMany heap environment (variable : rest) = do
  (address, next) <- must (Heap.importWithEnvironment heap environment (Var variable))
  (addresses, final) <- importMany heap next rest
  pure (address : addresses, final)

genVariables :: Gen [VarId]
genVariables = do
  count <- Gen.int (Range.linear 1 300)
  base <- Gen.int (Range.linear (-1000) 1000)
  stride <- Gen.int (Range.linear 1 31)
  descending <- Gen.bool
  let variables = [base + stride * index | index <- [0 .. count - 1]]
  pure (if descending then reverse variables else variables)

invalidAddress :: Either Heap.HeapError a -> Bool
invalidAddress (Left (Heap.InvalidAddress _)) = True
invalidAddress _ = False

prop_generated_environment_sharing :: Property
prop_generated_environment_sharing = withTests 150 . property $ do
  variables <- forAll genVariables
  value <- forAll (Gen.integral (Range.linear (-100000) 100000))
  let result = runST $ do
        heap <- Heap.newHeap
        (roots, environment) <- importMany heap Heap.emptyEnvironment variables
        scalar <- must (Heap.importTerm heap (IntLit value))
        forM_ roots $ \root -> must (Heap.unify heap root scalar)
        -- Bound references still validate, and source-ID lookup retains their
        -- original roots instead of allocating a second variable activation.
        top <- Heap.heapSize heap
        (repeated, _) <- importMany heap environment (reverse variables)
        finalTop <- Heap.heapSize heap
        exported <- must (Heap.exportTerms heap repeated)
        pure (repeated == reverse roots, finalTop == top, exported)
  result === (True, True, replicate (length variables) (IntLit value))

prop_generated_stale_frontier_atomic :: Property
prop_generated_stale_frontier_atomic = withTests 150 . property $ do
  variables <- forAll genVariables
  padding <- forAll (Gen.int (Range.linear 0 300))
  let result = runST $ do
        heap <- Heap.newHeap
        survivor <- must (Heap.newVariable heap)
        mark <- Heap.checkpoint heap
        (_, environment) <- importMany heap Heap.emptyEnvironment variables
        must (Heap.rollback heap mark)
        -- Reuse every discarded slot, plus optionally more, so bounds alone
        -- cannot detect the stale environment. Its variables are unused by
        -- the next import, which still has to fail before any allocation.
        forM_ [1 .. length variables + padding] $ \_ -> must (Heap.newVariable heap)
        size <- Heap.heapSize heap
        trail <- Heap.trailSize heap
        interns <- Heap.internSize heap
        rejected <- Heap.importWithEnvironment heap environment
          (Compound "unused_environment" [Atom "new_constant"])
        sizeAfter <- Heap.heapSize heap
        trailAfter <- Heap.trailSize heap
        internsAfter <- Heap.internSize heap
        alive <- must (Heap.exportTerm heap survivor)
        pure (invalidAddress rejected, size == sizeAfter, trail == trailAfter,
          interns == internsAfter, alive)
  result === (True, True, True, True, Var 0)

prop_generated_surviving_frontier :: Property
prop_generated_surviving_frontier = withTests 100 . property $ do
  variables <- forAll genVariables
  count <- forAll (Gen.int (Range.linear 1 300))
  let result = runST $ do
        heap <- Heap.newHeap
        (roots, environment) <- importMany heap Heap.emptyEnvironment variables
        mark <- Heap.checkpoint heap
        -- This returned environment gains no roots. Its term's allocations
        -- can disappear without invalidating the older variable activation.
        (_, sameRoots) <- must (Heap.importWithEnvironment heap environment
          (Compound "discarded" (map Var variables ++ replicate count (Atom "x"))))
        case roots of
          first : second : _ -> do
            _ <- must (Heap.unify heap first second)
            must (Heap.rerootVariable heap second)
          _ -> pure ()
        must (Heap.rollback heap mark)
        top <- Heap.heapSize heap
        (restored, _) <- importMany heap sameRoots variables
        after <- Heap.heapSize heap
        terms <- must (Heap.exportTerms heap restored)
        pure (restored == roots, after == top, terms)
  result === (True, True, map Var [0 .. length variables - 1])

prop_generated_paired_snapshots :: Property
prop_generated_paired_snapshots = withTests 100 . property $ do
  variables <- forAll genVariables
  value <- forAll (Gen.integral (Range.linear (-1000) 1000))
  let result = runST $ do
        heap <- Heap.newHeap
        (_, initialEnvironment) <- importMany heap Heap.emptyEnvironment variables
        initial <- Heap.freezeHeap heap
        let laterId = maximum variables + 1
        (leftRoot, leftEnvironment) <- must
          (Heap.importWithEnvironment heap initialEnvironment (Var laterId))
        leftValue <- must (Heap.importTerm heap (IntLit value))
        _ <- must (Heap.unify heap leftRoot leftValue)
        left <- Heap.freezeHeap heap
        Heap.restoreHeap heap initial
        -- A restored mutable heap never reuses an allocation's generation.
        (rightRoot, rightEnvironment) <- must
          (Heap.importWithEnvironment heap initialEnvironment (Var laterId))
        rightValue <- must (Heap.importTerm heap (IntLit (value + 1)))
        _ <- must (Heap.unify heap rightRoot rightValue)
        right <- Heap.freezeHeap heap
        observations <- forM [(left, leftEnvironment, rightEnvironment, value),
          (right, rightEnvironment, leftEnvironment, value + 1)] $
          \(snapshot, own, displaced, expected) -> do
            Heap.restoreHeap heap snapshot
            rejected <- Heap.importWithEnvironment heap displaced (Atom "unused")
            (root, _) <- must (Heap.importWithEnvironment heap own (Var laterId))
            actual <- must (Heap.exportTerm heap root)
            pure (invalidAddress rejected, actual == IntLit expected)
        Heap.restoreHeap heap initial
        (_, _) <- must (Heap.importWithEnvironment heap initialEnvironment (Atom "valid"))
        discarded <- Heap.importWithEnvironment heap leftEnvironment (Atom "unused")
        pure (observations, invalidAddress discarded)
  result === (replicate 2 (True, True), True)

prop_generated_frozen_forks :: Property
prop_generated_frozen_forks = withTests 100 . property $ do
  variables <- forAll genVariables
  values <- forAll (Gen.list (Range.singleton 3)
    (Gen.integral (Range.linear (-1000) 1000)))
  let result = runST $ do
        parent <- Heap.newHeap
        (roots, environment) <- importMany parent Heap.emptyEnvironment variables
        frozen <- Heap.freezeHeap parent
        branches <- forM values $ \value -> do
          heap <- Heap.thawHeap frozen
          let newId = maximum variables + 1
          (root, ownEnvironment) <- must
            (Heap.importWithEnvironment heap environment (Var newId))
          scalar <- must (Heap.importTerm heap (IntLit value))
          forM_ (root : roots) $ \address -> must (Heap.unify heap address scalar)
          snapshot <- Heap.freezeHeap heap
          pure (snapshot, ownEnvironment, newId, value)
        observations <- forM branches $ \(snapshot, own, newId, value) -> do
          heap <- Heap.thawHeap snapshot
          (newRoot, _) <- must (Heap.importWithEnvironment heap own (Var newId))
          actual <- must (Heap.exportTerms heap (newRoot : roots))
          pure (actual == replicate (length roots + 1) (IntLit value))
        parentTerms <- must (Heap.exportTerms parent roots)
        pure (observations, parentTerms)
  result === (replicate 3 True, map Var [0 .. length variables - 1])

prop_generated_successor_rejects_old_environment :: Property
prop_generated_successor_rejects_old_environment = withTests 100 . property $ do
  variables <- forAll genVariables
  let result = runST $ do
        previous <- Heap.newHeap
        (_, oldEnvironment) <- importMany previous Heap.emptyEnvironment variables
        replacement <- Heap.newHeapSuccessor previous
        (_, ownEnvironment) <- importMany replacement Heap.emptyEnvironment variables
        rejected <- Heap.importWithEnvironment replacement oldEnvironment (Atom "unused")
        (_, _) <- must (Heap.importWithEnvironment replacement ownEnvironment (Atom "valid"))
        pure (invalidAddress rejected)
  result === True

prop_generated_constructor_occurs_checks :: Property
prop_generated_constructor_occurs_checks = withTests 150 . property $ do
  depth <- forAll (Gen.int (Range.linear 0 60))
  width <- forAll (Gen.int (Range.linear 0 15))
  reversed <- forAll Gen.bool
  let wrap 0 child = child
      wrap count child = Compound "node"
        (wrap (count - 1) child : replicate width (Compound "literal" [IntLit 17]))
      term = wrap depth (Compound "pair" [Var 1, Atom "end"])
      result = runST $ do
        heap <- Heap.newHeap
        (roots, environment) <- importMany heap Heap.emptyEnvironment [0, 1]
        let (root, alias) = case roots of
              [first, second] -> (first, second)
              _ -> error "importing two variables changed their root count"
        (constructor, _) <- must (Heap.importWithEnvironment heap environment term)
        mark <- Heap.checkpoint heap
        _ <- must (Heap.unify heap root alias)
        -- Representatives can be changed independently of syntactic variable
        -- positions. Every nested variable occurrence must still participate
        -- in occurs checking after aliasing, rerooting, freezing and rollback.
        if reversed then must (Heap.rerootVariable heap alias) else pure ()
        snapshot <- Heap.freezeHeap heap
        accepted <- must (Heap.unify heap root constructor)
        thawed <- Heap.thawHeap snapshot
        thawedAccepted <- must (Heap.unify thawed root constructor)
        must (Heap.rollback heap mark)
        scalar <- must (Heap.importTerm heap (IntLit 23))
        _ <- must (Heap.unify heap alias scalar)
        grounded <- must (Heap.unify heap root constructor)
        terms <- must (Heap.exportTerms heap [root, alias])
        pure (accepted, thawedAccepted, grounded, terms)
      referenceAliased = Reference.unifyPlain Reference.emptySubst (Var 0) (Var 1)
      referenceCycle = referenceAliased >>= \subst -> Reference.unifyPlain subst (Var 0) term
      referenceGround = do
        subst <- Reference.unifyPlain Reference.emptySubst (Var 1) (IntLit 23)
        Reference.unifyPlain subst (Var 0) term
      expectedTerms = case referenceGround of
        Just subst -> case fst (Reference.canonicalize subst
          (Compound "$roots" [Var 0, Var 1])) of
          Compound _ terms -> terms
          _ -> error "canonicalizing roots changed their constructor"
        Nothing -> error "grounding fixture unexpectedly failed"
  assert (case referenceCycle of Nothing -> True; Just _ -> False)
  result === (False, False, True, expectedTerms)

prop_static_constructors_preserve_nan_comparison :: Property
prop_static_constructors_preserve_nan_comparison = withTests 1 . property $ do
  let result = runST $ do
        heap <- Heap.newHeap
        root <- must (Heap.newVariable heap)
        nan <- must (Heap.importTerm heap
          (Compound "ground" [Compound "nested" [FloatLit (0 / 0)]]))
        finite <- must (Heap.importTerm heap
          (Compound "ground" [Compound "nested" [FloatLit 7]]))
        mark <- Heap.checkpoint heap
        accepted <- must (Heap.unify heap root nan)
        before <- Heap.trailSize heap
        self <- must (Heap.unify heap root root)
        direct <- must (Heap.unify heap nan nan)
        after <- Heap.trailSize heap
        must (Heap.rollback heap mark)
        finiteAccepted <- must (Heap.unify heap root finite)
        finiteSelf <- must (Heap.unify heap root root)
        pure (accepted, self, direct, before == after, finiteAccepted, finiteSelf)
  result === (True, False, False, True, True, True)

-- Observe actual heap edges rather than only exported terms: a tree copier
-- could preserve all answers while duplicating every retained list suffix.
prop_generated_copy_preserves_suffix_sharing :: Property
prop_generated_copy_preserves_suffix_sharing = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 0 100))
  reverseIds <- forAll Gen.bool
  let chain 0 = Atom "end"
      chain n = Compound "cons" [IntLit (toInteger n), chain (n - 1)]
      variables = if reverseIds then reverse [0 .. count] else [0 .. count]
      suffixes heap address = do
        shape <- must (Heap.viewRaw heap address)
        case shape of
          Heap.CompoundView "cons" [_, rest] -> (address :) <$> suffixes heap rest
          Heap.AtomView "end" -> pure [address]
          _ -> error "chain fixture changed shape"
      result = runST $ do
        heap <- Heap.newHeap
        _ <- must (Heap.importTerm heap
          (Compound "garbage" (replicate 350 (Atom "discarded"))))
        root <- must (Heap.importTerm heap (chain count))
        tails <- suffixes heap root
        (roots, _) <- importMany heap Heap.emptyEnvironment variables
        forM_ (zip roots tails) $ \(variable, target) -> must (Heap.unify heap variable target)
        let supplied = roots ++ tails ++ [root, root]
        (copied, relocated) <- must (Heap.copyReachable heap supplied)
        let (copiedVariables, remainder) = splitAt (length roots) relocated
            (copiedTails, duplicates) = splitAt (length tails) remainder
        links <- forM copiedVariables $ \variable -> must (Heap.referenceTarget copied variable)
        let referenceLinks = links == map Just copiedTails
        chainLinks <- case copiedTails of
          first : _ -> (== copiedTails) <$> suffixes copied first
          _ -> error "copy lost chain root"
        size <- Heap.heapSize copied
        trail <- Heap.trailSize copied
        interns <- Heap.internSize copied
        environment <- must (Heap.environmentFromRoots copied
          (IM.fromList (zip variables copiedVariables)))
        (repeated, _) <- importMany copied environment variables
        after <- Heap.heapSize copied
        copiedValue <- case copiedTails of
          first : _ -> must (Heap.exportTerm copied first)
          _ -> error "copy lost chain root"
        pure (referenceLinks, chainLinks, size, trail, interns,
          repeated == copiedVariables, after == size,
          duplicates == take 1 copiedTails ++ take 1 copiedTails, copiedValue)
  result === (True, True, 3 * count + 2, 0,
    (count + 1, if count == 0 then 0 else 1), True, True, True, chain count)

prop_generated_copy_preserves_raw_aliases :: Property
prop_generated_copy_preserves_raw_aliases = withTests 100 . property $ do
  reverseAlias <- forAll Gen.bool
  count <- forAll (Gen.int (Range.linear 0 80))
  let wrap 0 term = term
      wrap n term = Compound "box" [wrap (n - 1) term]
      result = runST $ do
        heap <- Heap.newHeap
        (variables, environment) <- importMany heap Heap.emptyEnvironment [17, 3]
        let (first, second) = case variables of
              [a, b] -> (a, b)
              _ -> error "copy alias fixture lost variables"
        (syntax, _) <- must (Heap.importWithEnvironment heap environment
          (Compound ";" [Var 17, Atom "fallback"]))
        term <- must (Heap.importTerm heap (wrap count
          (Compound "->" [Atom "condition", Atom "then"])))
        _ <- must (Heap.unify heap first second)
        if reverseAlias then must (Heap.rerootVariable heap second) else pure ()
        beforeTarget <- must (Heap.referenceTarget heap first)
        let representative = if reverseAlias then second else first
        (copied, relocated) <- must (Heap.copyReachable heap [first, second, syntax, term])
        let (a, b, raw, value) = case relocated of
              [a', b', raw', value'] -> (a', b', raw', value')
              _ -> error "copy changed alias fixture root count"
        expectedTarget <- if beforeTarget == Just first then pure a else pure b
        afterTarget <- must (Heap.referenceTarget copied a)
        shape <- must (Heap.viewRaw copied raw)
        let preservesRaw = case shape of
              Heap.CompoundView ";" [variable, _] -> variable == a
              _ -> False
        base <- Heap.checkpoint copied
        _ <- must (Heap.unify copied a value)
        rawAfterBinding <- must (Heap.viewRaw copied raw)
        let stillRaw = case rawAfterBinding of
              Heap.CompoundView ";" [variable, _] -> variable == a
              _ -> False
        snapshot <- Heap.freezeHeap copied
        _ <- must (Heap.rollback copied base)
        freeAgain <- must (Heap.view copied a)
        resumed <- Heap.thawHeap snapshot
        resumedValue <- must (Heap.exportTerm resumed b)
        sourceFree <- must (Heap.view heap representative)
        pure (afterTarget == Just expectedTarget, preservesRaw, stillRaw,
          freeAgain == Heap.VariableView (if reverseAlias then b else a),
          resumedValue, sourceFree == Heap.VariableView representative)
  result === (True, True, True, True,
    wrap count (Compound "->" [Atom "condition", Atom "then"]), True)

prop_generated_copy_failure_is_atomic :: Property
prop_generated_copy_failure_is_atomic = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 1 300))
  let result = runST $ do
        heap <- Heap.newHeap
        root <- must (Heap.importTerm heap
          (Compound "kept" (map IntLit [1 .. toInteger count])))
        mark <- Heap.checkpoint heap
        discarded <- must (Heap.newVariable heap)
        must (Heap.rollback heap mark)
        _ <- must (Heap.newVariable heap)
        size <- Heap.heapSize heap
        trail <- Heap.trailSize heap
        interns <- Heap.internSize heap
        invalid <- Heap.copyReachable heap [root, discarded]
        sizeAfter <- Heap.heapSize heap
        trailAfter <- Heap.trailSize heap
        internsAfter <- Heap.internSize heap
        kept <- must (Heap.exportTerm heap root)
        (empty, emptyRoots) <- must (Heap.copyReachable heap [])
        emptySize <- Heap.heapSize empty
        emptyTrail <- Heap.trailSize empty
        emptyInterns <- Heap.internSize empty
        pure (invalidAddress invalid, size == sizeAfter, trail == trailAfter,
          interns == internsAfter, kept, null emptyRoots,
          emptySize, emptyTrail, emptyInterns)
  result === (True, True, True, True,
    Compound "kept" (map IntLit [1 .. toInteger count]), True, 0, 0, (0, 0))

prop_environment_reconstruction_validates_all_roots :: Property
prop_environment_reconstruction_validates_all_roots = withTests 1 . property $ do
  let result = runST $ do
        heap <- Heap.newHeap
        variable <- must (Heap.newVariable heap)
        scalar <- must (Heap.importTerm heap (Atom "value"))
        mark <- Heap.checkpoint heap
        discarded <- must (Heap.newVariable heap)
        must (Heap.rollback heap mark)
        replacement <- must (Heap.newVariable heap)
        invalid <- Heap.environmentFromRoots heap
          (IM.fromList [(0, discarded), (1, replacement)])
        wrongKind <- Heap.environmentFromRoots heap (IM.fromList [(0, variable), (1, scalar)])
        _ <- must (Heap.unify heap variable scalar)
        valid <- must (Heap.environmentFromRoots heap (IM.singleton 47 variable))
        (bound, _) <- must (Heap.importWithEnvironment heap valid (Var 47))
        copied <- must (Heap.exportTerm heap bound)
        let invalidKind = case wrongKind of
              Left Heap.IncompatibleBindings -> True
              _ -> False
        pure (invalidAddress invalid, invalidKind, bound == variable, copied)
  result === (True, True, True, Atom "value")

prop_copy_preserves_ground_nan_and_dynamic_occurs_checks :: Property
prop_copy_preserves_ground_nan_and_dynamic_occurs_checks = withTests 1 . property $ do
  let result = runST $ do
        heap <- Heap.newHeap
        (variable, environment) <- must
          (Heap.importWithEnvironment heap Heap.emptyEnvironment (Var 0))
        (dynamic, _) <- must (Heap.importWithEnvironment heap environment
          (Compound "dynamic" [Compound "box" [Var 0]]))
        ground <- must (Heap.importTerm heap
          (Compound "ground" [Compound "box" [FloatLit (0 / 0)]]))
        (copied, roots) <- must (Heap.copyReachable heap [variable, dynamic, ground])
        let (root, withVariable, withNaN) = case roots of
              [a, b, c] -> (a, b, c)
              _ -> error "copy changed occurs-check fixture root count"
        cycleAccepted <- must (Heap.unify copied root withVariable)
        nanAccepted <- must (Heap.unify copied root withNaN)
        nanSelf <- must (Heap.unify copied root root)
        nanDirect <- must (Heap.unify copied withNaN withNaN)
        original <- must (Heap.exportTerm heap variable)
        pure (cycleAccepted, nanAccepted, nanSelf, nanDirect, original)
  result === (False, True, False, False, Var 0)

machineEnvironmentGroup :: Group
machineEnvironmentGroup = Group "machine activation environment"
  [ ("generated_environment_sharing", prop_generated_environment_sharing),
    ("generated_stale_frontier_atomic", prop_generated_stale_frontier_atomic),
    ("generated_surviving_frontier", prop_generated_surviving_frontier),
    ("generated_paired_snapshots", prop_generated_paired_snapshots),
    ("generated_frozen_forks", prop_generated_frozen_forks),
    ("generated_successor_rejects_old_environment", prop_generated_successor_rejects_old_environment),
    ("generated_constructor_occurs_checks", prop_generated_constructor_occurs_checks),
    ("static_constructors_preserve_nan_comparison", prop_static_constructors_preserve_nan_comparison),
    ("generated_copy_preserves_suffix_sharing", prop_generated_copy_preserves_suffix_sharing),
    ("generated_copy_preserves_raw_aliases", prop_generated_copy_preserves_raw_aliases),
    ("generated_copy_failure_is_atomic", prop_generated_copy_failure_is_atomic),
    ("environment_reconstruction_validates_all_roots", prop_environment_reconstruction_validates_all_roots),
    ("copy_preserves_ground_nan_and_dynamic_occurs_checks", prop_copy_preserves_ground_nan_and_dynamic_occurs_checks)
  ]
