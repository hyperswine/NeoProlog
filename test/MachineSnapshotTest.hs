{-# LANGUAGE OverloadedStrings #-}

-- Installing a branch snapshot must restore every ownership component, while
-- snapshots and displaced futures keep their own immutable pages. Allocation
-- generations must continue increasing across restores into the same heap.
module MachineSnapshotTest (machineSnapshotGroup) where

import Control.Monad (forM, forM_)
import Control.Monad.ST (ST, runST)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax
import qualified Infera.Unify as Reference

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

must :: Show err => ST s (Either err a) -> ST s a
must action = action >>= either (error . show) pure

importRoots :: Heap.Heap s -> [Term] -> ST s [Heap.Address]
importRoots heap = go Heap.emptyEnvironment
  where
    go _ [] = pure []
    go environment (term : rest) = do
      (address, next) <- must (Heap.importWithEnvironment heap environment term)
      (address :) <$> go next rest

referenceRoots :: Reference.Subst -> [Term] -> [Term]
referenceRoots substitution roots = case fst (Reference.canonicalize substitution (Compound "$snapshot_roots" roots)) of
  Compound _ terms -> terms
  _ -> error "canonicalization changed a compound"

data Operation = Bind Int Int | Save | Restore Int
  deriving Show

genOperation :: Int -> Gen Operation
genOperation count = Gen.frequency
  [ (6, Bind <$> index <*> index), (2, pure Save), (3, Restore <$> Gen.int (Range.linear 0 20)) ]
  where
    index = Gen.int (Range.linear 0 (count - 1))

prop_generated_restore_branch_model :: Property
prop_generated_restore_branch_model = withTests 300 . property $ do
  let terms = map Var [0 .. 5] ++ map IntLit [0 .. 3]
      referenceStep substitution snapshots operations = case operations of
        [] -> []
        operation : rest ->
          let (next, saved, accepted) = case operation of
                Bind left right -> case Reference.unifyPlain substitution (terms !! left) (terms !! right) of
                  Nothing -> (substitution, snapshots, Just False)
                  Just result -> (result, snapshots, Just True)
                Save -> (substitution, substitution : snapshots, Nothing)
                Restore requested -> (snapshots !! (requested `mod` length snapshots), snapshots, Nothing)
           in (accepted, referenceRoots next terms) : referenceStep next saved rest
  operations <- forAll (Gen.list (Range.linear 1 60) (genOperation (length terms)))
  let actual = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        initial <- Heap.freezeHeap heap
        let step snapshots remaining = case remaining of
              [] -> pure []
              operation : rest -> do
                (saved, accepted) <- case operation of
                  Bind left right -> do
                    result <- must (Heap.unify heap (roots !! left) (roots !! right))
                    pure (snapshots, Just result)
                  Save -> do
                    frozen <- Heap.freezeHeap heap
                    pure (frozen : snapshots, Nothing)
                  Restore requested -> do
                    Heap.restoreHeap heap (snapshots !! (requested `mod` length snapshots))
                    pure (snapshots, Nothing)
                exported <- must (Heap.exportTerms heap roots)
                more <- step saved rest
                pure ((accepted, exported) : more)
        step [initial] operations
  actual === referenceStep Reference.emptySubst [Reference.emptySubst] operations

prop_restore_saved_checkpoint_lineage :: Property
prop_restore_saved_checkpoint_lineage = unit $ do
  let actual = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap [Var 0, Var 1, IntLit 4, IntLit 9]
        initial <- Heap.checkpoint heap
        _ <- must (Heap.unify heap (roots !! 0) (roots !! 2))
        middle <- Heap.checkpoint heap
        frozenMiddle <- Heap.freezeHeap heap
        _ <- must (Heap.unify heap (roots !! 1) (roots !! 3))
        frozenFinal <- Heap.freezeHeap heap
        Heap.restoreHeap heap frozenMiddle
        restoredMiddle <- must (Heap.exportTerms heap roots)
        must (Heap.rollback heap initial)
        restoredInitial <- must (Heap.exportTerms heap roots)
        Heap.restoreHeap heap frozenFinal
        restoredFinal <- must (Heap.exportTerms heap roots)
        must (Heap.rollback heap middle)
        rolledMiddle <- must (Heap.exportTerms heap roots)
        Heap.restoreHeap heap frozenMiddle
        must (Heap.rollback heap middle)
        sameMiddle <- must (Heap.exportTerms heap roots)
        pure (restoredMiddle, restoredInitial, restoredFinal, rolledMiddle, sameMiddle)
      initialTerms = [Var 0, Var 1, IntLit 4, IntLit 9]
      middleTerms = [IntLit 4, Var 0, IntLit 4, IntLit 9]
      finalTerms = [IntLit 4, IntLit 9, IntLit 4, IntLit 9]
  actual === (middleTerms, initialTerms, finalTerms, middleTerms, middleTerms)

prop_restores_do_not_revive_discarded_addresses :: Property
prop_restores_do_not_revive_discarded_addresses = unit $ do
  let actual = runST $ do
        heap <- Heap.newHeap
        root <- must (Heap.newVariable heap)
        frozen <- Heap.freezeHeap heap
        discarded <- must (Heap.newVariable heap)
        Heap.restoreHeap heap frozen
        replacement <- must (Heap.newVariable heap)
        staleFirst <- Heap.view heap discarded
        savedReplacement <- Heap.freezeHeap heap
        Heap.restoreHeap heap frozen
        newest <- must (Heap.newVariable heap)
        staleSecond <- Heap.view heap replacement
        Heap.restoreHeap heap savedReplacement
        restoredReplacement <- Heap.view heap replacement
        staleNewest <- Heap.view heap newest
        rootValue <- Heap.view heap root
        pure (replacement /= discarded, newest /= replacement,
          staleFirst == Left (Heap.InvalidAddress discarded),
          staleSecond == Left (Heap.InvalidAddress replacement),
          restoredReplacement == Right (Heap.VariableView replacement),
          staleNewest == Left (Heap.InvalidAddress newest),
          rootValue == Right (Heap.VariableView root))
  actual === (True, True, True, True, True, True, True)

prop_restore_replaces_frontiers_and_intern_tables :: Property
prop_restore_replaces_frontiers_and_intern_tables = unit $ do
  let actual = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap [Var 0, Compound "original" [Atom "before"]]
        initialSizes <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        frozen <- Heap.freezeHeap heap
        extra <- must (Heap.importTerm heap (Compound "later" [IntLit 100, StrLit "new"]))
        _ <- must (Heap.unify heap (roots !! 0) extra)
        futureSizes <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        future <- Heap.freezeHeap heap
        Heap.restoreHeap heap frozen
        restoredSizes <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        restoredRoots <- must (Heap.exportTerms heap roots)
        absentExtra <- Heap.view heap extra
        Heap.restoreHeap heap future
        futureRestoredSizes <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        futureExtra <- must (Heap.exportTerm heap extra)
        pure (initialSizes, restoredSizes, futureSizes, futureRestoredSizes, restoredRoots,
          absentExtra == Left (Heap.InvalidAddress extra), futureExtra)
  case actual of
    (before, restored, future, restoredFuture, roots, missing, extra) -> do
      restored === before
      restoredFuture === future
      roots === [Var 0, Compound "original" [Atom "before"]]
      missing === True
      extra === Compound "later" [IntLit 100, StrLit "new"]

prop_restore_multi_page_copy_on_write :: Property
prop_restore_multi_page_copy_on_write = unit $ do
  let count = 520
      terms = map Var [0 .. count - 1] ++ map (IntLit . fromIntegral) [0 .. count - 1]
      actual = runST $ do
        heap <- Heap.newHeap
        roots <- importRoots heap terms
        initial <- Heap.checkpoint heap
        frozen <- Heap.freezeHeap heap
        -- Cell and trail writes span several 256-entry pages. These roots
        -- retain their handles while each installed branch changes values.
        forM_ [0 .. count - 1] $ \index -> do
          _ <- must (Heap.unify heap (roots !! index) (roots !! (count + index)))
          pure ()
        first <- Heap.freezeHeap heap
        firstValues <- must (Heap.exportTerms heap (take count roots))
        Heap.restoreHeap heap frozen
        forM_ [0 .. count - 1] $ \index -> do
          _ <- must (Heap.unify heap (roots !! index) (roots !! (count + count - 1 - index)))
          pure ()
        second <- Heap.freezeHeap heap
        secondValues <- must (Heap.exportTerms heap (take count roots))
        Heap.restoreHeap heap first
        resumedFirst <- must (Heap.exportTerms heap (take count roots))
        must (Heap.rollback heap initial)
        restoredInitial <- must (Heap.exportTerms heap (take count roots))
        Heap.restoreHeap heap second
        resumedSecond <- must (Heap.exportTerms heap (take count roots))
        -- Thawing both retained snapshots proves subsequent restores and
        -- rollback did not mutate their immutable arrays.
        saved <- forM [first, second] $ \snapshot -> do
          other <- Heap.thawHeap snapshot
          must (Heap.exportTerms other (take count roots))
        pure (firstValues, secondValues, resumedFirst, resumedSecond, restoredInitial, saved)
      ascending = map (IntLit . fromIntegral) [0 .. count - 1]
      descending = reverse ascending
  actual === (ascending, descending, ascending, descending, map Var [0 .. count - 1], [ascending, descending])

prop_restore_into_successor_preserves_snapshot_handles :: Property
prop_restore_into_successor_preserves_snapshot_handles = unit $ do
  let actual = runST $ do
        previous <- Heap.newHeap
        roots <- importRoots previous [Var 0, Atom "value"]
        checkpoint <- Heap.checkpoint previous
        saved <- Heap.freezeHeap previous
        replacement <- Heap.newHeapSuccessor previous
        scratch <- must (Heap.newVariable replacement)
        Heap.restoreHeap replacement saved
        _ <- must (Heap.unify replacement (roots !! 0) (roots !! 1))
        bound <- must (Heap.exportTerms replacement roots)
        must (Heap.rollback replacement checkpoint)
        unbound <- must (Heap.exportTerms replacement roots)
        future <- must (Heap.newVariable replacement)
        stale <- Heap.view replacement scratch
        original <- must (Heap.exportTerms previous roots)
        pure (bound, unbound, original, future /= scratch, stale == Left (Heap.InvalidAddress scratch))
  actual === ([Atom "value", Atom "value"], [Var 0, Atom "value"], [Var 0, Atom "value"], True, True)

machineSnapshotGroup :: Group
machineSnapshotGroup = Group "machine snapshot restore"
  [ ("generated_restore_branch_model", prop_generated_restore_branch_model),
    ("restore_saved_checkpoint_lineage", prop_restore_saved_checkpoint_lineage),
    ("restores_do_not_revive_discarded_addresses", prop_restores_do_not_revive_discarded_addresses),
    ("restore_replaces_frontiers_and_intern_tables", prop_restore_replaces_frontiers_and_intern_tables),
    ("restore_multi_page_copy_on_write", prop_restore_multi_page_copy_on_write),
    ("restore_into_successor_preserves_snapshot_handles", prop_restore_into_successor_preserves_snapshot_handles)
  ]
