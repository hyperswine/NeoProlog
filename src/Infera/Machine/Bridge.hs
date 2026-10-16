-- | Immutable logical variable names at the boundary between the term heap
-- and the reference solver's complete persistent state. A 'Bindings' value
-- belongs to the same branch as its heap handles and must be checkpointed and
-- restored with that heap. No heap address is exported into a 'SolverState'.
module Infera.Machine.Bridge
  ( Bindings,
    newBindings,
    allocateActivation,
    lookupVariables,
    bindingCount,
    bindingVariables,
    rebuild,
    importTerms,
    normalizeTermGraph,
    exportTerms,
    exportRawTerms,
    exportState,
    syncState,
    syncAcceptedState,
    compareVariables,
    bindingChanges,
    syncBindings,
    syncAddedBindings,
  )
where

import Control.Monad (foldM, forM, unless, zipWithM_)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.ST (ST)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import GHC.Float (castDoubleToWord64)
import Infera.Arith (arithOps, evalArithSafe)
import Infera.CLP (Store (..), constraintVars)
import Infera.Engine.Reference (SolverState (..))
import Infera.Machine.Heap (Address, Heap, HeapError (..))
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax (Term (..), VarId, termVarIds)
import qualified Infera.Unify as Unify

data Bindings = Bindings !(IntMap Address) !(Map.Map Address VarId) !Heap.Environment

bindingCount :: Bindings -> Int
bindingCount (Bindings roots _ _) = IM.size roots

bindingVariables :: Bindings -> [VarId]
bindingVariables (Bindings roots _ _) = IM.keys roots

type BridgeM s = ExceptT HeapError (ST s)

checked :: ST s (Either HeapError a) -> BridgeM s a
checked action = lift action >>= either throwError pure

-- A multi-term import or synchronization is one transaction. Individual heap
-- operations also roll back locally, but a later mismatch must undo earlier
-- successful bindings and new logical variable roots as well.
atomic :: Heap s -> BridgeM s a -> ST s (Either HeapError a)
atomic heap action = do
  mark <- Heap.checkpoint heap
  result <- runExceptT action
  case result of
    Right value -> pure (Right value)
    Left err -> do
      restored <- Heap.rollback heap mark
      pure $ case restored of
        Left rollbackError -> Left rollbackError
        Right () -> Left err

newBindings :: Heap s -> [VarId] -> ST s (Either HeapError Bindings)
newBindings heap variables = atomic heap $
  extend heap (Bindings IM.empty Map.empty Heap.emptyEnvironment) variables

-- | Reserve one clause's local logical roots in ascending local-ID order.
-- Existing sparse IDs retain their identity, as in ordinary term import.
-- Only the local range is inspected; the environment's allocation-prefix
-- witness validates prior roots without rescanning historical activations.
-- The temporary wrapper contains variables only, never clause source terms.
allocateActivation :: Heap s -> Bindings -> VarId -> Int
  -> ST s (Either HeapError (Bindings, [Address]))
allocateActivation heap bindings base count
  | count <= 0 = pure (Left IncompatibleBindings)
  | base > maxBound - count = pure (Left HeapCapacityExceeded)
  | otherwise = importTerms heap bindings (map Var [base .. base + count - 1])

-- | Look up existing logical roots without allocating or extending an
-- activation. Missing IDs fail rather than recreating locals retired by
-- collection. Request order and duplicates are preserved, as are the raw
-- roots of bound aliases; this operation never dereferences a variable.
--
-- The environment's allocation-prefix witness is validated once even when
-- the request is empty, then every requested root and source ID is checked.
-- The bindings and heap must still belong to the same branch. This read-only
-- operation needs neither a checkpoint nor an imported wrapper term.
lookupVariables :: Heap s -> Bindings -> [VarId]
  -> ST s (Either HeapError [Address])
lookupVariables heap (Bindings roots names environment) variables = runExceptT $ do
  checked (Heap.validateEnvironment heap environment)
  forM variables $ \variable -> do
    address <- maybe (throwError IncompatibleBindings) pure (IM.lookup variable roots)
    unless (Map.lookup address names == Just variable) (throwError IncompatibleBindings)
    shape <- checked (Heap.viewRaw heap address)
    case shape of
      Heap.VariableView original | original == address -> pure address
      _ -> throwError IncompatibleBindings

-- | Rebuild at a deterministic collection safe point. The caller must prove
-- that every surviving rollback owner has its own immutable frozen heap;
-- no rollback mark may depend on the active mutable heap after rebuilding.
-- Every live active control handle must occur in the supplied list. Initial query/caller variable IDs are protected even
-- when absent from those control terms. Older frozen snapshots remain valid.
--
-- Only unreachable internal substitution entries are retired. Fresh-ID
-- counters and all other persistent solver metadata retain their values.
-- Following raw variable occurrences, rather than deep-walking terms, keeps
-- the syntax observed by shallow control matches and accepted alias IDs.
-- The old heap is untouched if any reconstruction step fails.
rebuild :: Heap s -> Bindings -> [VarId] -> SolverState -> [Address]
  -> ST s (Either HeapError (Heap s, Bindings, SolverState, [Address]))
rebuild heap bindings@(Bindings roots _ _) protected state controlRoots = runExceptT $ do
  syntax <- checked (exportRawTerms heap bindings controlRoots)
  let store = ssStore state
      substitution = stSubst store
      seeds = IS.fromList (protected ++ concatMap termVarIds syntax ++ storeVariables store)
      live = reachableVariables substitution seeds
      -- A strict fold constructs a new map without retaining a delayed
      -- filtering traversal over all historical activation bindings.
      retained = IM.foldlWithKey' (retain live) IM.empty substitution
      compacted = state {ssStore = store {stSubst = retained}}
      retain variables result variable term
        | IS.member variable variables = IM.insert variable term result
        | otherwise = result
  retained `seq` live `seq` pure ()
  let retainedRoots = IM.restrictKeys roots live
  unless (IM.keysSet retainedRoots == live) (throwError IncompatibleBindings)
  -- Copy the raw graph once. Exporting and reimporting every live root
  -- independently expands shared suffixes into separate trees at collection.
  -- Raw Ref links also retain the alias syntax expected by the CLP mirror.
  (nextHeap, addresses) <- checked
    (Heap.copyReachable heap (IM.elems retainedRoots ++ controlRoots))
  let (logicalRoots, relocated) = splitAt (IM.size retainedRoots) addresses
      nextRoots = IM.fromDistinctAscList (zip (IM.keys retainedRoots) logicalRoots)
      nextNames = Map.fromList [(address, variable) | (variable, address) <- IM.toAscList nextRoots]
  environment <- checked (Heap.environmentFromRoots nextHeap nextRoots)
  pure (nextHeap, Bindings nextRoots nextNames environment, compacted, relocated)

reachableVariables :: Unify.Subst -> IS.IntSet -> IS.IntSet
reachableVariables substitution initial = visit IS.empty (IS.toList initial)
  where
    visit seen [] = seen
    visit seen (variable : remaining)
      | IS.member variable seen = visit seen remaining
      | otherwise =
          let next = IS.insert variable seen
              children = maybe [] termVarIds (IM.lookup variable substitution)
           in next `seq` visit next (children ++ remaining)

-- Allocate missing roots in logical-ID order before importing user terms.
-- Importing one wrapper validates the old environment once and establishes
-- all sharing without repeatedly traversing an ever-growing environment.
extend :: Heap s -> Bindings -> [VarId] -> BridgeM s Bindings
extend heap bindings@(Bindings roots names environment) variables
  | null missing = pure bindings
  | otherwise = do
      (wrapper, nextEnvironment) <- checked $
        Heap.importWithEnvironment heap environment
          (Compound "$machine_bridge_roots" (map Var missing))
      shape <- checked (Heap.view heap wrapper)
      case shape of
        Heap.CompoundView _ addresses -> pure $
          Bindings (IM.union roots (IM.fromList (zip missing addresses)))
            (Map.union names (Map.fromList (zip addresses missing))) nextEnvironment
        _ -> throwError IncompatibleBindings
  where
    missing = IS.toAscList (IS.filter (\variable -> IM.notMember variable roots) (IS.fromList variables))

importTerms :: Heap s -> Bindings -> [Term] -> ST s (Either HeapError (Bindings, [Address]))
importTerms _ bindings [] = pure (Right (bindings, []))
importTerms heap (Bindings roots names environment) terms = atomic heap $ do
  -- Put missing variables first in logical-ID order, then import all terms
  -- in one activation. This validates the existing environment once rather
  -- than once per head/body term while preserving the variable ordering.
  (wrapper, nextEnvironment) <- checked $ Heap.importWithEnvironment heap environment
    (Compound "$machine_bridge_terms" (map Var missing ++ terms))
  shape <- checked (Heap.view heap wrapper)
  case shape of
    Heap.CompoundView _ addresses -> do
      let (newRoots, imported) = splitAt (length missing) addresses
          nextRoots = IM.union roots (IM.fromList (zip missing newRoots))
          nextNames = Map.union names (Map.fromList (zip newRoots missing))
      pure (Bindings nextRoots nextNames nextEnvironment, imported)
    _ -> throwError IncompatibleBindings
  where
    missing = IS.toAscList (IS.filter (\variable -> IM.notMember variable roots)
      (IS.fromList (concatMap termVarIds terms)))

-- | Match 'Infera.Arith.normArithTerm' on a raw term graph without expanding
-- shared suffixes into independent imported trees. Bound reference chains
-- collapse to their normalized targets; free references keep their exact
-- accepted logical identities. Unchanged constructors and scalar handles are
-- reused, and each unique raw address is visited once in this transaction.
--
-- Children are normalized before arithmetic is folded. A child that remains
-- a variable or symbolic constructor cannot yield a numeric value, so its
-- parent also stays symbolic; arithmetic errors likewise remain syntax.
-- Folding numeric scalar children uses the same evaluator as normArithTerm.
-- The complete operation rolls back allocations if any handle is invalid.
normalizeTermGraph :: Heap s -> Bindings -> Address -> ST s (Either HeapError Address)
normalizeTermGraph heap (Bindings _ names _) root = atomic heap $
  fst . fst <$> normalize Map.empty root
  where
    normalize memo address = case Map.lookup address memo of
      Just result -> pure (result, memo)
      Nothing -> do
        shape <- checked (Heap.viewRaw heap address)
        (result, next) <- case shape of
          Heap.VariableView original -> do
            unless (Map.member original names) (throwError IncompatibleBindings)
            target <- checked (Heap.referenceTarget heap address)
            case target of
              Just bound | bound /= address -> normalize memo bound
              Just _ -> pure ((address, Nothing), memo)
              Nothing -> throwError IncompatibleBindings
          Heap.IntegerView value -> pure ((address, Just (IntLit value)), memo)
          Heap.FloatView value -> pure ((address, Just (FloatLit value)), memo)
          Heap.CompoundView name children -> do
            (values, normalizedMemo) <- normalizeChildren memo children
            let normalized = map fst values
                numeric = if name `elem` arithOps then traverse snd values else Nothing
                folded = numeric >>= \arguments -> case evalArithSafe Unify.emptySubst (Compound name arguments) of
                  Right (Just value) -> Just value
                  _ -> Nothing
            case folded of
              Just value -> do
                scalar <- checked (Heap.importTerm heap value)
                pure ((scalar, Just value), normalizedMemo)
              Nothing -> do
                constructor <- if normalized == children then pure address
                  else checked (Heap.newCompound heap name normalized)
                pure ((constructor, Nothing), normalizedMemo)
          _ -> pure ((address, Nothing), memo)
        let updated = Map.insert address result next
        updated `seq` pure (result, updated)
    normalizeChildren memo [] = pure ([], memo)
    normalizeChildren memo (address : rest) = do
      (value, next) <- normalize memo address
      (values, final) <- normalizeChildren next rest
      pure (value : values, final)

-- Every free heap variable has a stable logical root in Bindings. Export its
-- actual identity, including an accepted startup alias directed at a larger
-- ID; replacing it with a smaller class member would change residuals and
-- the store's watched-variable identities.
exportTerms :: Heap s -> Bindings -> [Address] -> ST s (Either HeapError [Term])
exportTerms heap bindings extra = runExceptT $ mapM (exportValue heap bindings) extra

-- | Preserve the original variable occurrences of syntax rather than
-- dereferencing them. The supplied complete SolverState performs shallow
-- walking when a reference builtin runs. In particular, a variable bound to
-- an if-then term must not turn a plain disjunction into if-then-else merely
-- because an adapter exported its arguments deeply.
exportRawTerms :: Heap s -> Bindings -> [Address] -> ST s (Either HeapError [Term])
exportRawTerms heap (Bindings _ names _) addresses = runExceptT $ mapM exportOne addresses
  where
    exportOne address = do
      shape <- checked (Heap.viewRaw heap address)
      case shape of
        Heap.VariableView original -> case Map.lookup original names of
          Just variable -> pure (Var variable)
          Nothing -> throwError IncompatibleBindings
        Heap.AtomView scalar -> pure (Atom scalar)
        Heap.IntegerView scalar -> pure (IntLit scalar)
        Heap.FloatView scalar -> pure (FloatLit scalar)
        Heap.CharacterView scalar -> pure (CharLit scalar)
        Heap.StringView scalar -> pure (StrLit scalar)
        Heap.CompoundView name children -> Compound name <$> mapM exportOne children

exportAll :: Heap s -> Bindings -> [Address] -> BridgeM s (IntMap Term, [Term])
exportAll heap (Bindings roots _ _) extra = do
  terms <- checked (Heap.exportTerms heap (IM.elems roots ++ extra))
  let (rootTerms, extraTerms) = splitAt (IM.size roots) terms
      representatives = freeRepresentatives (IM.keys roots) rootTerms
  namedRoots <- mapM (relabel representatives) rootTerms
  namedExtra <- mapM (relabel representatives) extraTerms
  pure (IM.fromDistinctAscList (zip (IM.keys roots) namedRoots), namedExtra)

freeRepresentatives :: [VarId] -> [Term] -> IntMap VarId
freeRepresentatives variables terms = IM.fromListWith min
  [(free, variable) | (variable, Var free) <- zip variables terms]

relabel :: IntMap VarId -> Term -> BridgeM s Term
relabel representatives term = case term of
  Var variable -> case IM.lookup variable representatives of
    Just logical -> pure (Var logical)
    Nothing -> throwError IncompatibleBindings
  Compound name arguments -> Compound name <$> mapM (relabel representatives) arguments
  scalar -> pure scalar

logicalSubst :: IntMap Term -> Unify.Subst
logicalSubst = IM.filterWithKey (\variable term -> case term of
  Var same -> variable /= same
  _ -> True)

-- Only the substitution crosses representations. Its bound compounds must
-- retain raw variable occurrences: shallow control matches distinguish a
-- syntactic variable bound to (C -> T) from a literal (C -> T) inside (;).
-- Domains, propagators, pending/dirty sets, output, tables and dynamic facts
-- retain their complete immutable reference versions without reconstruction.
exportState :: Heap s -> Bindings -> SolverState -> ST s (Either HeapError SolverState)
exportState heap bindings@(Bindings roots rawNames _) state = runExceptT $ do
  resolved <- forM (IM.toAscList roots) $ \(variable, address) -> do
    shape <- checked (Heap.view heap address)
    pure (variable, address, shape)
  entries <- forM resolved $ \(variable, address, shape) -> do
    term <- case shape of
      Heap.VariableView target -> case Map.lookup target rawNames of
        Just representative -> pure (Var representative)
        Nothing -> throwError IncompatibleBindings
      _ -> do
        reference <- checked (Heap.referenceTarget heap address)
        case reference of
          Just target -> case Map.lookup target rawNames of
            Just logical -> pure (Var logical)
            Nothing -> exportRaw target
          Nothing -> exportRaw address
    pure (variable, term)
  pure state {ssStore = (ssStore state)
    {stSubst = logicalSubst (IM.fromDistinctAscList entries)}}
  where
    exportRaw address = do
      terms <- checked (exportRawTerms heap bindings [address])
      case terms of
        [term] -> pure term
        _ -> throwError IncompatibleBindings

-- | Reconcile an accepted reference state with the heap. This is state
-- synchronization, not another execution of the original unification goal:
-- unchanged NaNs must survive even though language-level NaN unification
-- fails. Bind only free roots, then validate the complete resulting state.
-- An already-bound compound's free children each have their own logical root.
syncState :: Heap s -> Bindings -> SolverState -> ST s (Either HeapError Bindings)
syncState heap bindings state = atomic heap $ do
  extended@(Bindings roots _ _) <- extend heap bindings (stateVariables state)
  (before, _) <- exportAll heap extended []
  let current = logicalSubst before
      incoming = stSubst (ssStore state)
      changes =
        [ (variable, term)
        | (variable, term) <- IM.toAscList incoming,
          let normalized = Unify.deepWalk current term,
          not (sameTermBits (IM.findWithDefault (Var variable) variable before) normalized)
        ]
  final <- foldM (synchronize heap) extended changes
  let variables = IM.keys roots
      wanted = map (Unify.deepWalk incoming . Var) variables
      freeRoots = IS.toAscList (IS.fromList [variable | Var variable <- wanted])
  -- The full accepted substitution, unlike a new language-level merge,
  -- determines its own representative identities. Canonical equivalence
  -- alone is insufficient: domains and dependency sets still use those IDs.
  mapM_ (\variable -> do
    address <- maybe (throwError IncompatibleBindings) pure (IM.lookup variable roots)
    checked (Heap.rerootVariable heap address)) freeRoots
  after <- mapM (exportValue heap final) (IM.elems roots)
  zipWithM_ (\actual expected -> unless (sameTermBits actual expected)
    (throwError IncompatibleBindings)) after wanted
  pure final

-- | Fast internal boundary for a state already accepted by the reference
-- resolver. The supplied previous state must mirror this heap, and incoming
-- must extend its substitution without replacing existing raw bindings.
-- Occurs-checked unification binds only free representatives; propagation
-- likewise inserts singleton bindings only for still-free roots. Native
-- scopes protect all caller IDs during collection, so their accepted child
-- states retain the caller's bindings. Retain the complete new persistent
-- store and extend its logical roots; public/untrusted startup states
-- continue to use 'syncState' and its whole-state validation.
syncAcceptedState :: Heap s -> Bindings -> SolverState -> SolverState -> ST s (Either HeapError Bindings)
syncAcceptedState heap bindings previous incoming = atomic heap $ do
  -- ssFresh records all allocations, including retired activations. Only
  -- actually referenced IDs can become live again at an accepted boundary.
  -- Existing raw substitution entries already have roots in bindings. The
  -- monotone extension importer below installs every new key and every raw
  -- variable in its new value, including nested aliases. Only free metadata
  -- roots can arrive without occurring in those substitutions. Rescanning
  -- all old compound values here repeatedly expands shared grid suffixes.
  extended <- extend heap bindings (storeVariables (ssStore incoming))
  checked (syncAddedBindings heap extended (stSubst (ssStore previous)) (stSubst (ssStore incoming)))

synchronize :: Heap s -> Bindings -> (VarId, Term) -> BridgeM s Bindings
synchronize heap bindings@(Bindings roots _ _) (variable, term) = do
  address <- maybe (throwError IncompatibleBindings) pure (IM.lookup variable roots)
  shape <- checked (Heap.view heap address)
  case shape of
    Heap.VariableView _ -> do
      (updated, addresses) <- checked (importTerms heap bindings [term])
      case addresses of
        [target] -> do
          (matches, _) <- checked (Heap.unifyWithChanges (compareVariables updated) heap address target)
          unless matches (throwError IncompatibleBindings)
          pure updated
        _ -> throwError IncompatibleBindings
    _ -> pure bindings

-- | Order unbound references by stable logical ID, including IDs created
-- after a findall whose retained variables can exceed ssFresh. Heap handles
-- outside this bridge are rejected when their binding changes are exported.
compareVariables :: Bindings -> Address -> Address -> Ordering
compareVariables (Bindings _ names _) left right =
  case (Map.lookup left names, Map.lookup right names) of
    (Just a, Just b) -> compare a b
    _ -> compare left right

-- | Export precisely the variable writes made by a successful heap unify.
-- Targets retain their raw syntax, so shallow callable/control matching sees
-- the same variable occurrences as the reference substitution.
bindingChanges :: Heap s -> Bindings -> [Address] -> ST s (Either HeapError [(VarId, Term)])
bindingChanges heap bindings@(Bindings _ names _) addresses = runExceptT $
  forM addresses $ \address -> do
    variable <- maybe (throwError IncompatibleBindings) pure (Map.lookup address names)
    target <- checked (Heap.referenceTarget heap address)
    case target of
      Just root | root /= address -> do
        terms <- checked (exportRawTerms heap bindings [root])
        case terms of
          [term] -> pure (variable, term)
          _ -> throwError IncompatibleBindings
      _ -> throwError IncompatibleBindings

-- | Apply only bindings added by a persistent-store operation. Existing
-- values are not language-unified again: an unchanged NaN must survive state
-- reconciliation. Validation covers the changed roots after all new free
-- roots have been bound, avoiding a full export of every historical clause
-- variable at each propagation step.
syncBindings :: Heap s -> Bindings -> Unify.Subst -> Unify.Subst -> ST s (Either HeapError Bindings)
syncBindings heap bindings previous incoming = atomic heap $ do
  unless (IM.null (IM.difference previous incoming)) (throwError IncompatibleBindings)
  let changes = IM.toAscList $ IM.differenceWith
        (\new old -> if sameTermBits new old then Nothing else Just new) incoming previous
  updated@(Bindings roots _ _) <- installBindings heap bindings changes
  mapM_ (validate updated roots) changes
  pure updated
  where
    validate updated roots (variable, _) = do
      address <- maybe (throwError IncompatibleBindings) pure (IM.lookup variable roots)
      actual <- exportValue heap updated address
      let expected = Unify.deepWalk incoming (Var variable)
      unless (sameTermBits actual expected) (throwError IncompatibleBindings)

-- | Trusted internal boundary for a monotone substitution extension. The
-- previous substitution must mirror the heap, and existing keys must retain
-- their exact raw terms. Native occurs-checked writes and CLP singleton
-- propagation satisfy that contract: only previously free representatives
-- acquire entries. Accepted native child states have the same property.
--
-- This is not an arbitrary-state validation API. Removed keys are rejected,
-- but retained values are not compared or deeply re-exported. Doing so would
-- repeatedly expand every historical alias into the same shared graph.
-- Use 'syncBindings' or 'syncState' when the extension proof is unavailable.
syncAddedBindings :: Heap s -> Bindings -> Unify.Subst -> Unify.Subst -> ST s (Either HeapError Bindings)
syncAddedBindings heap bindings previous incoming = atomic heap $ do
  unless (IM.null (IM.difference previous incoming)) (throwError IncompatibleBindings)
  installBindings heap bindings (IM.toAscList (IM.difference incoming previous))

-- Import all missing variable roots before installing any new raw binding.
-- Stable logical IDs, including noncanonical accepted aliases, remain the
-- source of reference ordering. Heap unification retains atomic rollback and
-- occurs checking; callers decide whether a deep validation is also needed.
installBindings :: Heap s -> Bindings -> [(VarId, Term)] -> BridgeM s Bindings
installBindings _ bindings [] = pure bindings
installBindings heap bindings changes = do
  let variables = map fst changes
      terms = map snd changes
  (updated@(Bindings roots _ _), imported) <- checked $
    importTerms heap bindings (map Var variables ++ terms)
  let targets = drop (length variables) imported
  zipWithM_ (bind updated roots) changes targets
  pure updated
  where
    bind updated roots (variable, _) target = do
      address <- maybe (throwError IncompatibleBindings) pure (IM.lookup variable roots)
      shape <- checked (Heap.view heap address)
      case shape of
        Heap.VariableView _ -> do
          (matches, _) <- checked (Heap.unifyWithChanges (compareVariables updated) heap address target)
          unless matches (throwError IncompatibleBindings)
        _ -> pure ()

exportValue :: Heap s -> Bindings -> Address -> BridgeM s Term
exportValue heap bindings@(Bindings _ names _) address = do
  shape <- checked (Heap.view heap address)
  case shape of
    Heap.VariableView root -> maybe (throwError IncompatibleBindings) (pure . Var) (Map.lookup root names)
    Heap.AtomView scalar -> pure (Atom scalar)
    Heap.IntegerView scalar -> pure (IntLit scalar)
    Heap.FloatView scalar -> pure (FloatLit scalar)
    Heap.CharacterView scalar -> pure (CharLit scalar)
    Heap.StringView scalar -> pure (StrLit scalar)
    Heap.CompoundView name children -> Compound name <$> mapM (exportValue heap bindings) children

stateVariables :: SolverState -> [VarId]
stateVariables state =
  [0 .. ssFresh state - 1] ++ referencedStateVariables state

referencedStateVariables :: SolverState -> [VarId]
referencedStateVariables state =
  IM.keys substitution
    ++ concatMap termVarIds (IM.elems substitution)
    ++ storeVariables store
  where
    store = ssStore state
    substitution = stSubst store

-- Pending/dependency values are constraint IDs; only their variable keys,
-- constraint terms and dirty/watched sets belong in the logical root set.
-- Table and dynamic-fact terms have their own canonical variable namespaces.
storeVariables :: Store -> [VarId]
storeVariables store =
  IM.keys (stDomains store)
    ++ concatMap constraintVars (stConstraints store)
    ++ concatMap constraintVars (IM.elems (stConstraintMap store))
    ++ IS.toList (stWatched store)
    ++ IM.keys (stDependencies store)
    ++ IS.toList (stDirtyVars store)

-- Term's derived Eq makes NaNs unequal to themselves and treats signed zero
-- as equal. State reconciliation needs exact immutable scalar identity.
sameTermBits :: Term -> Term -> Bool
sameTermBits (Atom left) (Atom right) = left == right
sameTermBits (Var left) (Var right) = left == right
sameTermBits (IntLit left) (IntLit right) = left == right
sameTermBits (FloatLit left) (FloatLit right) =
  castDoubleToWord64 left == castDoubleToWord64 right
sameTermBits (CharLit left) (CharLit right) = left == right
sameTermBits (StrLit left) (StrLit right) = left == right
sameTermBits (Compound leftName left) (Compound rightName right) =
  leftName == rightName && length left == length right && and (zipWith sameTermBits left right)
sameTermBits _ _ = False
