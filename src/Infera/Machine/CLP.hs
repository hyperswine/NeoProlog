-- | Native heap bindings with the existing persistent CLP propagation store.
-- Stable logical IDs connect heap references to watched variables. Every
-- operation either accepts the heap and complete store together or restores
-- the heap prefix; no reference goal evaluator participates in this layer.
module Infera.Machine.CLP
  ( unify,
    apply,
    applyAccepted,
    bindInteger,
  )
where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.ST (ST)
import Control.Monad.Trans.Class (lift)
import qualified Data.IntMap.Strict as IM
import Data.List (foldl')
import Infera.CLP (Store (..))
import qualified Infera.CLP as CLP
import Infera.Error (SolveError)
import qualified Infera.Machine.Bridge as Bridge
import Infera.Machine.Heap (Address, Heap, HeapError (..))
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax (Term (..), VarId)

type Result = Either SolveError (Maybe (Bridge.Bindings, Store))
type BindingM s = ExceptT HeapError (ST s)

checked :: ST s (Either HeapError a) -> BindingM s a
checked action = lift action >>= either throwError pure

-- Failed propagation must undo even successful bindings preceding the
-- contradiction. The caller retains its original immutable store/map.
transaction :: Heap s -> BindingM s Result -> ST s (Either HeapError Result)
transaction heap action = do
  mark <- Heap.checkpoint heap
  result <- runExceptT action
  case result of
    Right (Right (Just _)) -> pure result
    _ -> do
      restored <- Heap.rollback heap mark
      pure $ case restored of
        Left err -> Left err
        Right () -> result

-- | Unify through the heap, then wake persistent-store dependencies from the
-- exact reference writes. This also maintains the substitution mirror when
-- no constraints are active, so later posting needs no full heap export.
unify :: Heap s -> Bridge.Bindings -> Store -> Address -> Address -> ST s (Either HeapError Result)
unify heap bindings store left right = transaction heap $ do
  (accepted, written) <- checked $
    Heap.unifyWithChanges (Bridge.compareVariables bindings) heap left right
  if not accepted
    then pure (Right Nothing)
    else do
      changes <- checked (Bridge.bindingChanges heap bindings written)
      let mirrored = foldl' (\substitution (variable, term) -> IM.insert variable term substitution)
            (stSubst store) changes
          propagated = CLP.applyBindings changes store
      -- The heap already contains every write in changes. Without a watched
      -- write, applyBindings cannot propagate any additional bindings, so the
      -- complete returned store already mirrors this heap. Comparing its
      -- entire substitution again makes ordinary clause calls quadratic in
      -- the number of preceding activations.
      if any (CLP.isConstrained store . fst) changes
        then reconcileAdded heap bindings mirrored propagated
        else pure (fmap (fmap (\updated -> (bindings, updated))) propagated)

-- | Post/narrow constraints using the existing persistent algorithms, then
-- install newly propagated singleton bindings on the native heap. Arbitrary
-- callbacks retain strict reconciliation of changed existing bindings.
apply :: Heap s -> Bridge.Bindings -> Store -> (Store -> Either SolveError (Maybe Store)) -> ST s (Either HeapError Result)
apply heap bindings store operation = transaction heap $
  reconcile heap bindings (stSubst store) (operation store)

-- | Internal operation whose accepted substitution is known to extend the
-- previous raw bindings without replacement. The driver supplies the CLP
-- posting algorithms, or a selected minimum state descended from this store.
-- Propagation binds only still-free representatives. Callers without that
-- proof must use 'apply', which validates arbitrary accepted callbacks.
applyAccepted :: Heap s -> Bridge.Bindings -> Store -> (Store -> Either SolveError (Maybe Store)) -> ST s (Either HeapError Result)
applyAccepted heap bindings store operation = transaction heap $
  reconcileAdded heap bindings (stSubst store) (operation store)

-- | Label one stable logical variable with an integer. Imports are covered
-- by the same transaction as unification and propagation.
bindInteger :: Heap s -> Bridge.Bindings -> Store -> VarId -> Integer -> ST s (Either HeapError Result)
bindInteger heap bindings store variable value = transaction heap $ do
  (imported, addresses) <- checked $ Bridge.importTerms heap bindings [Var variable, IntLit value]
  case addresses of
    [left, right] -> checked (unify heap imported store left right)
    _ -> throwError IncompatibleBindings

reconcile :: Heap s -> Bridge.Bindings -> IM.IntMap Term -> Either SolveError (Maybe Store) -> BindingM s Result
reconcile _ _ _ (Left err) = pure (Left err)
reconcile _ _ _ (Right Nothing) = pure (Right Nothing)
reconcile heap bindings previous (Right (Just store)) = do
  synchronized <- checked (Bridge.syncBindings heap bindings previous (stSubst store))
  pure (Right (Just (synchronized, store)))

reconcileAdded :: Heap s -> Bridge.Bindings -> IM.IntMap Term -> Either SolveError (Maybe Store) -> BindingM s Result
reconcileAdded _ _ _ (Left err) = pure (Left err)
reconcileAdded _ _ _ (Right Nothing) = pure (Right Nothing)
reconcileAdded heap bindings previous (Right (Just store)) = do
  -- Native heap writes and the persistent propagator bind only previously
  -- free representatives, so accepted stores extend raw substitution entries
  -- without replacing old terms. Avoid revalidating every shared old graph.
  synchronized <- checked (Bridge.syncAddedBindings heap bindings previous (stSubst store))
  pure (Right (Just (synchronized, store)))
