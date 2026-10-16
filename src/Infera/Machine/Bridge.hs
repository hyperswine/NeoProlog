-- | Immutable logical variable names at the boundary between the term heap
-- and the reference solver's complete persistent state. A 'Bindings' value
-- belongs to the same branch as its heap handles and must be checkpointed and
-- restored with that heap. No heap address is exported into a 'SolverState'.
module Infera.Machine.Bridge
  ( Bindings,
    newBindings,
    importTerms,
    exportTerms,
    exportRawTerms,
    exportState,
    syncState,
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
import Infera.CLP (Store (..), constraintVars)
import Infera.Engine (SolverState (..))
import Infera.Machine.Heap (Address, Heap, HeapError (..))
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax (Term (..), VarId, termVarIds)
import qualified Infera.Unify as Unify

data Bindings = Bindings !(IntMap Address) !Heap.Environment

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
  extend heap (Bindings IM.empty Heap.emptyEnvironment) variables

-- Allocate missing roots in logical-ID order before importing user terms.
-- Importing one wrapper validates the old environment once and establishes
-- all sharing without repeatedly traversing an ever-growing environment.
extend :: Heap s -> Bindings -> [VarId] -> BridgeM s Bindings
extend heap bindings@(Bindings roots environment) variables
  | null missing = pure bindings
  | otherwise = do
      (wrapper, nextEnvironment) <- checked $
        Heap.importWithEnvironment heap environment
          (Compound "$machine_bridge_roots" (map Var missing))
      shape <- checked (Heap.view heap wrapper)
      case shape of
        Heap.CompoundView _ addresses -> pure $
          Bindings (IM.union roots (IM.fromList (zip missing addresses))) nextEnvironment
        _ -> throwError IncompatibleBindings
  where
    missing = IS.toAscList (IS.difference (IS.fromList variables) (IM.keysSet roots))

importTerms :: Heap s -> Bindings -> [Term] -> ST s (Either HeapError (Bindings, [Address]))
importTerms heap bindings terms = atomic heap $ do
  extended <- extend heap bindings (concatMap termVarIds terms)
  (final, reversed) <- foldM add (extended, []) terms
  pure (final, reverse reversed)
  where
    add (Bindings roots environment, addresses) term = do
      (address, nextEnvironment) <- checked (Heap.importWithEnvironment heap environment term)
      pure (Bindings roots nextEnvironment, address : addresses)

-- Use every logical root in one export so free variables inside structures
-- share the same renaming as query roots and issue terms. Every free heap
-- variable has a root in Bindings; absence therefore signals a foreign handle.
exportTerms :: Heap s -> Bindings -> [Address] -> ST s (Either HeapError [Term])
exportTerms heap bindings extra = runExceptT $ do
  (_, terms) <- exportAll heap bindings extra
  pure terms

-- | Preserve the original variable occurrences of syntax rather than
-- dereferencing them. The supplied complete SolverState performs shallow
-- walking when a reference builtin runs. In particular, a variable bound to
-- an if-then term must not turn a plain disjunction into if-then-else merely
-- because an adapter exported its arguments deeply.
exportRawTerms :: Heap s -> Bindings -> [Address] -> ST s (Either HeapError [Term])
exportRawTerms heap (Bindings roots _) addresses = runExceptT $ mapM exportOne addresses
  where
    names = Map.fromListWith min [(address, variable) | (variable, address) <- IM.toAscList roots]
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
exportAll heap (Bindings roots _) extra = do
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
exportState heap bindings@(Bindings roots _) state = runExceptT $ do
  resolved <- forM (IM.toAscList roots) $ \(variable, address) -> do
    shape <- checked (Heap.view heap address)
    pure (variable, address, shape)
  let freeNames = Map.fromListWith min
        [(target, variable) | (variable, _, Heap.VariableView target) <- resolved]
      rawNames = Map.fromListWith min
        [(address, variable) | (variable, address) <- IM.toAscList roots]
  entries <- forM resolved $ \(variable, address, shape) -> do
    term <- case shape of
      Heap.VariableView target -> case Map.lookup target freeNames of
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
  extended@(Bindings roots _) <- extend heap bindings (stateVariables state)
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
  (after, _) <- exportAll heap final []
  let variables = IM.keys roots
      wanted = map (Unify.deepWalk incoming . Var) variables
      representatives = freeRepresentatives variables wanted
  namedWanted <- mapM (relabel representatives) wanted
  zipWithM_ (\actual expected -> unless (sameTermBits actual expected)
    (throwError IncompatibleBindings)) (IM.elems after) namedWanted
  pure final

synchronize :: Heap s -> Bindings -> (VarId, Term) -> BridgeM s Bindings
synchronize heap bindings@(Bindings roots _) (variable, term) = do
  address <- maybe (throwError IncompatibleBindings) pure (IM.lookup variable roots)
  shape <- checked (Heap.view heap address)
  case shape of
    Heap.VariableView _ -> do
      (updated, addresses) <- checked (importTerms heap bindings [term])
      case addresses of
        [target] -> do
          matches <- checked (Heap.unify heap address target)
          unless matches (throwError IncompatibleBindings)
          pure updated
        _ -> throwError IncompatibleBindings
    _ -> pure bindings

stateVariables :: SolverState -> [VarId]
stateVariables state =
  [0 .. ssFresh state - 1]
    ++ IM.keys substitution
    ++ concatMap termVarIds (IM.elems substitution)
    ++ IM.keys (stDomains store)
    ++ concatMap constraintVars (stConstraints store)
    ++ concatMap constraintVars (IM.elems (stConstraintMap store))
    ++ IS.toList (stWatched store)
    ++ IM.keys (stDependencies store)
    ++ IS.toList (stDirtyVars store)
  where
    store = ssStore state
    substitution = stSubst store

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
