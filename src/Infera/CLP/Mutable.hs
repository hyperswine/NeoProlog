{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Trailed constraint state for the native engine. Substitution, domains,
-- dependencies and constraints live in independently mutable sparse cells.
-- The work queues and the common linear reducer operate on these cells without
-- constructing persistent Stores. A Store is materialized only at an API
-- boundary or for a complex single-constraint reducer.
module Infera.CLP.Mutable
  ( MutableStore, Mark, new, newWithStats, freeze, replaceStore, mark, rollback,
    commit, historySize, storageSizes,
    changesSince, watchedSince, getSubst, walk, deepWalk, domainOf, watched, constraintCount,
    statistics, storeUnify, applyBindings, storeBind, addRelation, addDiseq,
    addDomain, addDomains, addAllDifferent, addReified, propagate,
  ) where

import Control.Monad (foldM, forM_, unless, when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.IORef
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.List (foldl')
import qualified Data.Set as Set
import Infera.Arith (evalIntExpr)
import Infera.CLP (Bound (..), Constraint (..), Domain (..), LinExpr (..),
                   ReductionOutcome (..), Reduced (..), Rel (..), Store (..), fullDomain)
import qualified Infera.CLP as P
import Infera.Error (SolveError (..))
import Infera.Syntax (Term (..), VarId)
import Infera.Unify (Subst)
import qualified Infera.Unify as U

data Variable = Variable !(Maybe Term) !(Maybe Domain) !IntSet
data Undo = Undo !(IO ()) !(Maybe VarId) !(Maybe IntSet)
newtype Mark = Mark Int deriving (Eq, Ord, Show)
data Residuals = Original [Constraint] | Derived

data MutableStore = MutableStore
  { variables :: !(IORef (IntMap (IORef Variable))),
    constraints :: !(IORef (IntMap (IORef (Maybe Constraint)))),
    pending :: !(IORef IntSet),
    dirty :: !(IORef IntSet),
    watchSet :: !(IORef IntSet),
    nextConstraint :: !(IORef Int),
    count :: !(IORef Int),
    trail :: !(IORef [Undo]),
    depth :: !(IORef Int),
    changedVars :: !(IORef IntSet),
    changedSubst :: !(IORef IntSet),
    changedConstraints :: !(IORef IntSet),
    residuals :: !(IORef Residuals),
    cachedSubst :: !(IORef Subst),
    cachedStore :: !(IORef Store),
    counters :: !(Maybe (IORef (Int, Int, Int)))
  }

data Failure = Failed | Raised SolveError
type M = ExceptT Failure IO
type Checked = IO (Either SolveError Bool)

new :: Store -> IO MutableStore
new = newWithStats False

newWithStats :: Bool -> Store -> IO MutableStore
newWithStats collectStats st = do
  let ids = IM.keysSet (stSubst st) `IS.union` IM.keysSet (stDomains st)
            `IS.union` IM.keysSet (stDependencies st)
  cells <- forMIds ids $ \v -> newIORef (Variable (IM.lookup v (stSubst st))
                   (IM.lookup v (stDomains st)) (IM.findWithDefault IS.empty v (stDependencies st)))
  cs <- traverse (newIORef . Just) (stConstraintMap st)
  stats <- if collectStats then Just <$> newIORef (0,0,0) else pure Nothing
  MutableStore <$> newIORef cells <*> newIORef cs
    <*> newIORef (stPending st) <*> newIORef (stDirtyVars st)
    <*> newIORef (stWatched st) <*> newIORef (stNextConstraint st)
    <*> newIORef (stConstraintCount st) <*> newIORef [] <*> newIORef 0
    <*> newIORef IS.empty <*> newIORef IS.empty <*> newIORef IS.empty
    <*> newIORef (Original (stConstraints st)) <*> newIORef (stSubst st) <*> newIORef st
    <*> pure stats

forMIds :: IntSet -> (Int -> IO a) -> IO (IntMap a)
forMIds ids action = IM.fromAscList <$> mapM (\v -> (,) v <$> action v) (IS.toAscList ids)

mark :: MutableStore -> IO Mark
mark ms = Mark <$> readIORef (depth ms)

-- | Discard undo history when the caller has no outstanding marks. This
-- invalidates every previously issued mark, including marks at depth zero;
-- retain the returned mark as the new root. Live state, frozen snapshots and
-- diagnostic counters are unchanged. A caller with live alternatives must
-- keep the history until those alternatives have been discarded.
commit :: MutableStore -> IO Mark
commit ms = do
  size <- historySize ms
  when (size /= 0) $ do
    writeIORef (trail ms) []
    writeIORef (depth ms) 0
  pure (Mark 0)

historySize :: MutableStore -> IO Int
historySize = readIORef . depth

-- | Live sparse variable and constraint cells, excluding undo history and
-- cached immutable snapshots. Useful for checking deterministic reclamation.
storageSizes :: MutableStore -> IO (Int, Int)
storageSizes ms = (,) <$> (IM.size <$> readIORef (variables ms))
                      <*> (IM.size <$> readIORef (constraints ms))

record :: MutableStore -> Maybe VarId -> IO () -> IO ()
record ms variable undo = do
  modifyIORef' (trail ms) (Undo undo variable Nothing :)
  modifyIORef' (depth ms) (+ 1)

rollback :: MutableStore -> Mark -> IO ()
rollback ms (Mark target) = go
  where
    go = do
      current <- readIORef (depth ms)
      when (current > target) $ do
        entries <- readIORef (trail ms)
        case entries of
          [] -> error "Infera.CLP.Mutable: missing undo entry"
          Undo undo _ _ : rest -> do
            undo
            writeIORef (trail ms) rest
            writeIORef (depth ms) (current - 1)
            go

-- Final values of the substitution cells actually touched after a mark.
-- Domain-only propagation writes do not cause redundant native bindings.
changesSince :: MutableStore -> Mark -> IO [(VarId, Term)]
changesSince ms (Mark start) = do
  current <- readIORef (depth ms)
  entries <- readIORef (trail ms)
  let touched = IS.fromList [v | Undo _ (Just v) _ <- take (max 0 (current - start)) entries]
  fmap concat $ mapM (\v -> do
    Variable value _ _ <- readVariable ms v
    pure (maybe [] (\t -> [(v, t)]) value)) (IS.toAscList touched)

watchedSince :: MutableStore -> Mark -> IO IntSet
watchedSince ms (Mark start) = do
  current <- readIORef (depth ms)
  entries <- readIORef (trail ms)
  now <- watched ms
  let original = foldl' (\acc (Undo _ _ old) -> maybe acc Just old) Nothing
        (take (max 0 (current-start)) entries)
  pure (maybe IS.empty (IS.difference now) original)

setWatched :: MutableStore -> IntSet -> IO ()
setWatched ms value = do
  old <- watched ms
  unless (old == value) $ do
    modifyIORef' (trail ms) (Undo (writeIORef (watchSet ms) old) Nothing (Just old) :)
    modifyIORef' (depth ms) (+1)
    writeIORef (watchSet ms) value

setResiduals :: MutableStore -> Residuals -> IO ()
setResiduals ms value = do
  old <- readIORef (residuals ms)
  record ms Nothing (writeIORef (residuals ms) old)
  writeIORef (residuals ms) value

touchVariable :: MutableStore -> VarId -> Bool -> IO ()
touchVariable ms v substitution = do
  modifyIORef' (changedVars ms) (IS.insert v)
  when substitution (modifyIORef' (changedSubst ms) (IS.insert v))

getVariable :: MutableStore -> VarId -> IO (IORef Variable)
getVariable ms v = do
  cells <- readIORef (variables ms)
  case IM.lookup v cells of
    Just cell -> pure cell
    Nothing -> do
      cell <- newIORef (Variable Nothing Nothing IS.empty)
      record ms Nothing $ do
        modifyIORef' (variables ms) (IM.delete v)
        touchVariable ms v True
      writeIORef (variables ms) (IM.insert v cell cells)
      touchVariable ms v True
      pure cell

readVariable :: MutableStore -> VarId -> IO Variable
readVariable ms v = do
  cells <- readIORef (variables ms)
  maybe (pure (Variable Nothing Nothing IS.empty)) readIORef (IM.lookup v cells)

writeVariable :: MutableStore -> VarId -> Variable -> IO ()
writeVariable ms v value@(Variable s d deps) = do
  cell <- getVariable ms v
  previous@(Variable oldS oldD oldDeps) <- readIORef cell
  unless (s == oldS && d == oldD && deps == oldDeps) $ do
    let substitution = s /= oldS
    record ms (if substitution then Just v else Nothing) $ do
      writeIORef cell previous
      touchVariable ms v substitution
    writeIORef cell value
    touchVariable ms v substitution

setRef :: Eq a => MutableStore -> IORef a -> a -> IO ()
setRef ms ref value = do
  old <- readIORef ref
  unless (old == value) $ do
    record ms Nothing (writeIORef ref old)
    writeIORef ref value

modifyRef :: Eq a => MutableStore -> IORef a -> (a -> a) -> IO ()
modifyRef ms ref f = readIORef ref >>= setRef ms ref . f

getConstraint :: MutableStore -> Int -> IO (Maybe Constraint)
getConstraint ms cid = do
  cells <- readIORef (constraints ms)
  maybe (pure Nothing) readIORef (IM.lookup cid cells)

setConstraint :: MutableStore -> Int -> Maybe Constraint -> IO ()
setConstraint ms cid value = do
  cells <- readIORef (constraints ms)
  case (IM.lookup cid cells, value) of
    (Nothing, Nothing) -> touchConstraint ms cid
    (Nothing, Just _) -> do
      ref <- newIORef value
      record ms Nothing $ do
        modifyIORef' (constraints ms) (IM.delete cid)
        touchConstraint ms cid
      writeIORef (constraints ms) (IM.insert cid ref cells)
      touchConstraint ms cid
    (Just cell, Nothing) -> do
      -- The undo entry keeps the old cell alive only while an alternative
      -- can still need it. The live index never accumulates empty CID slots.
      record ms Nothing $ do
        modifyIORef' (constraints ms) (IM.insert cid cell)
        touchConstraint ms cid
      writeIORef (constraints ms) (IM.delete cid cells)
      touchConstraint ms cid
    (Just cell, Just _) -> do
      old <- readIORef cell
      unless (old == value) $ do
        record ms Nothing $ do
          writeIORef cell old
          touchConstraint ms cid
        writeIORef cell value
        touchConstraint ms cid

-- A constraint posted and dropped between freezes needs no snapshot delta.
-- The same rule applies while undoing a branch, including a CID that was
-- frozen on the branch and therefore does need deleting from the cache.
touchConstraint :: MutableStore -> Int -> IO ()
touchConstraint ms cid = do
  cells <- readIORef (constraints ms)
  snapshot <- readIORef (cachedStore ms)
  modifyIORef' (changedConstraints ms)
    (if IM.notMember cid cells && IM.notMember cid (stConstraintMap snapshot)
      then IS.delete cid else IS.insert cid)

getSubst :: MutableStore -> IO Subst
getSubst ms = do
  changed <- readIORef (changedSubst ms)
  previous <- readIORef (cachedSubst ms)
  result <- foldM (\acc v -> do
    Variable value _ _ <- readVariable ms v
    pure (maybe (IM.delete v acc) (\t -> IM.insert v t acc) value)) previous (IS.toAscList changed)
  writeIORef (cachedSubst ms) result
  writeIORef (changedSubst ms) IS.empty
  pure result

freeze :: MutableStore -> IO Store
freeze ms = do
  previous <- readIORef (cachedStore ms)
  changed <- readIORef (changedVars ms)
  (domains, dependencies) <- foldM update (stDomains previous, stDependencies previous) (IS.toAscList changed)
  changedCs <- readIORef (changedConstraints ms)
  cmap <- foldM (\acc cid -> do
    value <- getConstraint ms cid
    pure (maybe (IM.delete cid acc) (\c -> IM.insert cid c acc) value))
      (stConstraintMap previous) (IS.toAscList changedCs)
  substitution <- getSubst ms
  watchedIds <- watched ms
  queued <- readIORef (pending ms)
  dirtyIds <- readIORef (dirty ms)
  next <- readIORef (nextConstraint ms)
  size <- constraintCount ms
  residualState <- readIORef (residuals ms)
  let residualList = case residualState of Original xs -> xs; Derived -> map snd (IM.toDescList cmap)
      result = Store substitution domains residualList watchedIds cmap dependencies queued dirtyIds next size
  writeIORef (cachedStore ms) result
  writeIORef (changedVars ms) IS.empty
  writeIORef (changedConstraints ms) IS.empty
  pure result
  where
    update (domains, dependencies) v = do
      Variable _ value deps <- readVariable ms v
      pure (maybe (IM.delete v domains) (\d -> IM.insert v d domains) value,
            if IS.null deps then IM.delete v dependencies else IM.insert v deps dependencies)

-- Import snapshots through the same undo log as native propagation. In
-- particular, importing an optimization winner must not invalidate choices
-- outside that optimization scope.
replaceStore :: MutableStore -> Store -> IO ()
replaceStore ms st = do
  old <- freeze ms
  let ids = IM.keysSet (stSubst old) `IS.union` IM.keysSet (stSubst st)
        `IS.union` IM.keysSet (stDomains old) `IS.union` IM.keysSet (stDomains st)
        `IS.union` IM.keysSet (stDependencies old) `IS.union` IM.keysSet (stDependencies st)
  forM_ (IS.toAscList ids) $ \v -> writeVariable ms v
    (Variable (IM.lookup v (stSubst st)) (IM.lookup v (stDomains st))
      (IM.findWithDefault IS.empty v (stDependencies st)))
  let cids = IM.keysSet (stConstraintMap old) `IS.union` IM.keysSet (stConstraintMap st)
  forM_ (IS.toAscList cids) $ \cid -> setConstraint ms cid (IM.lookup cid (stConstraintMap st))
  setWatched ms (stWatched st)
  setRef ms (pending ms) (stPending st)
  setRef ms (dirty ms) (stDirtyVars st)
  setRef ms (nextConstraint ms) (stNextConstraint st)
  setRef ms (count ms) (stConstraintCount st)
  -- Public Stores may deliberately carry a list awaiting propagate/reindex.
  setResiduals ms (Original (stConstraints st))

walk :: MutableStore -> Term -> IO Term
walk ms term@(Var v) = do
  Variable binding _ _ <- readVariable ms v
  maybe (pure term) (walk ms) binding
walk _ term = pure term

deepWalk :: MutableStore -> Term -> IO Term
deepWalk ms term = do
  result <- walk ms term
  case result of
    Compound name args -> Compound name <$> mapM (deepWalk ms) args
    _ -> pure result

domainOf :: MutableStore -> VarId -> IO (Maybe Domain)
domainOf ms v = do Variable _ value _ <- readVariable ms v; pure value

watched :: MutableStore -> IO IntSet
watched = readIORef . watchSet

constraintCount :: MutableStore -> IO Int
constraintCount = readIORef . count

statistics :: MutableStore -> IO (Int, Int, Int)
statistics ms = maybe (pure (0,0,0)) readIORef (counters ms)

tick :: MutableStore -> ((Int,Int,Int) -> (Int,Int,Int)) -> IO ()
tick ms increment = case counters ms of
  Nothing -> pure ()
  Just ref -> modifyIORef' ref increment

atomic :: MutableStore -> M () -> Checked
atomic ms action = do
  entry <- mark ms
  result <- runExceptT action
  case result of
    Right () -> pure (Right True)
    Left failure -> do
      rollback ms entry
      pure $ case failure of Failed -> Right False; Raised err -> Left err

liftEither :: Either SolveError a -> M a
liftEither = either (throwError . Raised) pure

require :: Bool -> M ()
require yes = unless yes (throwError Failed)

watch :: MutableStore -> [VarId] -> IO ()
watch ms ids = do
  old <- watched ms
  let added = filter (`IS.notMember` old) ids
  unless (null added) (setWatched ms (foldl' (flip IS.insert) old added))

markDirty :: MutableStore -> [VarId] -> IO ()
markDirty ms ids = do
  watch ms ids
  modifyRef ms (dirty ms) (\old -> foldl' (flip IS.insert) old ids)

putSubst :: MutableStore -> VarId -> Term -> IO ()
putSubst ms v value = do
  Variable _ d deps <- readVariable ms v
  writeVariable ms v (Variable (Just value) d deps)

putDomain :: MutableStore -> VarId -> Domain -> IO ()
putDomain ms v value = do
  Variable s old deps <- readVariable ms v
  unless (old == Just value) $ do
    writeVariable ms v (Variable s (Just value) deps)
    markDirty ms [v]

removeDomain :: MutableStore -> VarId -> IO ()
removeDomain ms v = do
  Variable s _ deps <- readVariable ms v
  writeVariable ms v (Variable s Nothing deps)
  markDirty ms [v]

constraintIds :: Constraint -> IntSet
constraintIds = IS.fromList . P.constraintVars

-- Updating a retained constraint in place has the same dependency index as
-- unregister/register, without recording temporary count and dependency edits.
replaceConstraint :: MutableStore -> Int -> Maybe Constraint -> Maybe Constraint -> IO ()
replaceConstraint ms cid old value = do
  let before = maybe IS.empty constraintIds old
      after = maybe IS.empty constraintIds value
  forM_ (IS.toAscList (before `IS.difference` after)) $ \v -> do
    Variable s d deps <- readVariable ms v
    writeVariable ms v (Variable s d (IS.delete cid deps))
  forM_ (IS.toAscList (after `IS.difference` before)) $ \v -> do
    Variable s d deps <- readVariable ms v
    writeVariable ms v (Variable s d (IS.insert cid deps))
  watch ms (IS.toAscList after)
  setConstraint ms cid value
  let presence Nothing = 0; presence (Just _) = 1
  modifyRef ms (count ms) (+ (presence value - presence old))

post :: MutableStore -> Constraint -> IO ()
post ms c = do
  cid <- readIORef (nextConstraint ms)
  setRef ms (nextConstraint ms) (cid + 1)
  replaceConstraint ms cid Nothing (Just c)
  modifyRef ms (pending ms) (IS.insert cid)

relation :: MutableStore -> Rel -> Term -> Term -> IO Constraint
relation ms rel a b = do
  substitution <- getSubst ms
  case P.linearize substitution (Compound "minus" [a, b]) of
    Just le -> pure (CLinear rel le)
    Nothing -> CNonLinear rel <$> deepWalk ms a <*> deepWalk ms b

addRelation :: MutableStore -> Rel -> Term -> Term -> Checked
addRelation ms rel a b = atomic ms $ do
  c <- liftIO (relation ms rel a b)
  liftIO (post ms c)
  runPropagation ms

addDiseq :: MutableStore -> Term -> Term -> Checked
addDiseq ms a b = atomic ms $ do
  c <- liftIO (CDiseq <$> deepWalk ms a <*> deepWalk ms b)
  liftIO (post ms c)
  runPropagation ms

addAllDifferent :: MutableStore -> [Term] -> Checked
addAllDifferent ms terms = atomic ms $ do
  ts <- liftIO (mapM (deepWalk ms) terms)
  let integerItem (Var _) = True
      integerItem t = case evalIntExpr U.emptySubst t of Right (Just _) -> True; _ -> False
  when (length ts > 1) $
    if all integerItem ts
      then liftIO (post ms (CAllDifferent ts)) >> runPropagation ms
      else forM_ [(a, b) | (i, a) <- zip [0 :: Int ..] ts, b <- drop (i + 1) ts] $ \(a,b) -> do
        c <- liftIO (relation ms RelNe a b)
        liftIO (post ms c)
        runPropagation ms

addReified :: MutableStore -> Rel -> Term -> Term -> Term -> Checked
addReified ms rel a b truth = atomic ms $ do
  c <- liftIO (CReified rel <$> deepWalk ms a <*> deepWalk ms b <*> deepWalk ms truth)
  liftIO (post ms c)
  runPropagation ms

addDomain :: MutableStore -> Term -> Bound -> Bound -> Checked
addDomain ms t lo hi = addDomains ms [t] lo hi

addDomains :: MutableStore -> [Term] -> Bound -> Bound -> Checked
addDomains ms ts lo hi = atomic ms (go ts)
  where
    go [] = runPropagation ms
    go (t : rest) = do
      active <- liftIO (constraintCount ms)
      -- Defer a malformed later list item until the earlier prefix has had
      -- its opportunity to fail, matching the persistent posting boundary.
      restricted <- liftIO (runExceptT (restrictTerm ms t lo hi))
      case restricted of
        Left (Raised err) | active == 0 -> runPropagation ms >> throwError (Raised err)
        Left failure -> throwError failure
        Right () -> do
          when (active > 0) (runPropagation ms)
          go rest

restrictTerm :: MutableStore -> Term -> Bound -> Bound -> M ()
restrictTerm ms term lo hi = do
  value <- liftIO (walk ms term)
  case value of
    IntLit n -> require (domainMember n (normDomain (Domain lo hi Set.empty)))
    Var v -> do
      old <- liftIO (getDomain ms v)
      let d = intersectDomain old (Domain lo hi Set.empty)
      require (not (domainEmpty d))
      liftIO (putDomain ms v d)
    other -> throwError (Raised (CLPTypeError other))

-- Occurs-checked unification is native as well; this avoids materializing the
-- complete persistent substitution before each labeling assignment.
storeUnify :: MutableStore -> Term -> Term -> Checked
storeUnify ms a b = atomic ms $ do
  bound <- unify ms [] a b
  watchers <- liftIO (watched ms)
  when (any (`IS.member` watchers) bound) $ do
    liftIO (markDirty ms bound)
    runPropagation ms

storeBind :: MutableStore -> VarId -> Integer -> Checked
storeBind ms v n = storeUnify ms (Var v) (IntLit n)

applyBindings :: MutableStore -> [(VarId, Term)] -> Checked
applyBindings ms changes = atomic ms $ do
  liftIO (forM_ changes (uncurry (putSubst ms)))
  watchers <- liftIO (watched ms)
  let bound = map fst changes
  when (any (`IS.member` watchers) bound) $ do
    liftIO (markDirty ms bound)
    runPropagation ms

unify :: MutableStore -> [VarId] -> Term -> Term -> M [VarId]
unify ms bound a b = do
  x <- liftIO (walk ms a)
  y <- liftIO (walk ms b)
  case (x, y) of
    (Var v, Var w)
      | v == w -> pure bound
      | v > w -> bind v (Var w)
      | otherwise -> bind w (Var v)
    (Var v, t) -> occurs ms v t >>= \cyclic -> require (not cyclic) >> bind v t
    (t, Var v) -> occurs ms v t >>= \cyclic -> require (not cyclic) >> bind v t
    (Compound f xs, Compound g ys)
      | f == g && length xs == length ys -> foldM (\acc (u,v) -> unify ms acc u v) bound (zip xs ys)
    _ -> require (x == y) >> pure bound
  where
    bind v term = liftIO (putSubst ms v term) >> pure (v : bound)

occurs :: MutableStore -> VarId -> Term -> M Bool
occurs ms variable term = do
  value <- liftIO (walk ms term)
  case value of
    Var v -> pure (v == variable)
    Compound _ args -> anyM (occurs ms variable) args
    _ -> pure False

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM f (x:xs) = f x >>= \yes -> if yes then pure True else anyM f xs

propagate :: MutableStore -> Checked
propagate ms = atomic ms $ do
  st <- liftIO (freeze ms)
  let base = st {stConstraintMap = IM.empty, stDependencies = IM.empty,
                stPending = IS.empty, stNextConstraint = 0, stConstraintCount = 0}
  liftIO (replaceStore ms base)
  liftIO (forM_ (reverse (stConstraints st)) (post ms))
  liftIO (markDirty ms (IM.keys (stDomains st) ++ IM.keys (stSubst st)))
  runPropagation ms

runPropagation :: MutableStore -> M ()
runPropagation ms = do
  initial <- liftIO (constraintCount ms)
  liftIO (tick ms (\(a,b,c) -> (a+1,b,c)))
  loop (500 * max 1 initial)
  where
    loop !remaining = do
      settleDirty ms
      queued <- liftIO (readIORef (pending ms))
      case IS.maxView queued of
        _ | remaining <= 0 -> finish
        Nothing -> finish
        Just (cid, rest) -> do
          liftIO (setRef ms (pending ms) rest)
          current <- liftIO (getConstraint ms cid)
          case current of
            Nothing -> loop remaining
            Just c -> do
              outcome <- reduce ms c
              liftIO (replaceConstraint ms cid (Just c) (case outcome of Drop -> Nothing; Keep next -> Just next))
              loop (remaining - 1)
    finish = liftIO (setResiduals ms Derived)

settleDirty :: MutableStore -> M ()
settleDirty ms = do
  changed <- liftIO (readIORef (dirty ms))
  unless (IS.null changed) $ do
    liftIO $ do
      queued <- readIORef (pending ms)
      awakened <- foldM (\ids v -> do
        Variable _ _ deps <- readVariable ms v
        pure (IS.union ids deps)) queued (IS.toAscList changed)
      setRef ms (pending ms) awakened
      setRef ms (dirty ms) IS.empty
    mapM_ settle (IS.toAscList changed)
    settleDirty ms
  where
    settle v = do
      value <- liftIO (domainOf ms v)
      case value of
        Nothing -> pure ()
        Just d -> do
          require (not (domainEmpty d))
          target <- liftIO (walk ms (Var v))
          case target of
            IntLit n -> require (domainMember n d) >> liftIO (removeDomain ms v)
            Var w | w /= v -> do
              old <- liftIO (getDomain ms w)
              let merged = intersectDomain old d
              require (not (domainEmpty merged))
              liftIO (removeDomain ms v >> putDomain ms w merged)
            Var _ | Just n <- domainSingleton d ->
              liftIO (putSubst ms v (IntLit n) >> removeDomain ms v)
            Var _ -> pure ()
            other -> throwError (Raised (CLPTypeError other))

reduce :: MutableStore -> Constraint -> M ReductionOutcome
reduce ms c = case c of
  CLinear rel le -> do
    liftIO (tick ms (\(a,b,counter) -> (a,b+1,counter)))
    reduced <- substituteLin ms le
    let coefs = leCoefs reduced
        k = leConst reduced
    if IM.null coefs
      then require (holds rel k) >> pure Drop
      else case rel of
        RelNe | [(v, cv)] <- IM.toList coefs -> do
          when (negate k `mod` cv == 0) $ do
            old <- liftIO (getDomain ms v)
            let d = normDomain old {domHoles = Set.insert (negate k `div` cv) (domHoles old)}
            require (not (domainEmpty d))
            liftIO (putDomain ms v d)
          pure Drop
        RelNe -> pure (Keep (CLinear rel reduced))
        _ -> do
          propagateBounds ms rel reduced
          pure (if IM.size coefs == 1 then Drop else Keep (CLinear rel reduced))
  CNonLinear rel a b -> do
    substitution <- liftIO (getSubst ms)
    case P.linearize substitution (Compound "minus" [a,b]) of
      Just le -> liftIO (watch ms (IM.keys (leCoefs le))) >> reduce ms (CLinear rel le)
      Nothing -> complex
  _ -> complex
  where
    complex = do
      liftIO (tick ms (\(a,b,counter) -> (a,b,counter+1)))
      snapshot <- liftIO (freeze ms)
      result <- liftEither (P.reduce snapshot c)
      case result of
        ReducedFail -> throwError Failed
        ReducedOK outcome updated -> do
          liftIO (importReduced ms snapshot updated)
          pure outcome

-- The pure single-step reducer either posts replacement pair constraints
-- (the symbolic all-different fallback), or changes only domains, watched
-- variables and the dirty set. It never binds substitutions or settles the
-- propagation queue itself. In the ordinary case all domain writes are named
-- in stDirtyVars, so importing a complex reduction touches only those cells,
-- rather than scanning every domain, dependency and constraint in the Store.
-- A changed next ID identifies the posting case, which needs the full import.
-- In this hybrid path every newly watched variable is also dirty: domain
-- writes use putDomain/markDirty. The pure reducer's other watch site is its
-- nonlinear-to-linear conversion, which 'reduce' intercepts natively above.
-- Nested reification constructs its ordinary relation under the unchanged
-- substitution and cannot introduce another such conversion in this step.
-- Consequently watching these dirty IDs preserves the exact watched superset
-- without comparing the entire, commonly unchanged stWatched set each visit.
importReduced :: MutableStore -> Store -> Store -> IO ()
importReduced ms before after
  | stNextConstraint before /= stNextConstraint after = replaceStore ms after
  | otherwise = do
      forM_ (IS.toAscList (stDirtyVars after)) $ \v -> do
        Variable substitution _ dependencies <- readVariable ms v
        writeVariable ms v (Variable substitution (IM.lookup v (stDomains after)) dependencies)
      watch ms (IS.toAscList (stDirtyVars after))
      setRef ms (dirty ms) (stDirtyVars after)

substituteLin :: MutableStore -> LinExpr -> M LinExpr
substituteLin ms (LinExpr coefs k0) = go (IM.toAscList coefs) IM.empty k0
  where
    go [] acc k = pure (LinExpr (IM.filter (/= 0) acc) k)
    go ((v, coefficient):rest) acc k = do
      term <- liftIO (walk ms (Var v))
      case term of
        IntLit n -> go rest acc (k + coefficient*n)
        Var w -> go rest (IM.insertWith (+) w coefficient acc) k
        other -> throwError (Raised (CLPTypeError other))

data Total = Total !Integer !Int !Int

adjustTotal :: Int -> Bound -> Total -> Total
adjustTotal delta bound (Total finite negative positive) = case bound of
  Fin n -> Total (finite + fromIntegral delta*n) negative positive
  NegInf -> Total finite (negative+delta) positive
  PosInf -> Total finite negative (positive+delta)

totalBound :: Total -> Bound
totalBound (Total finite negative positive)
  | negative > 0 = NegInf
  | positive > 0 = PosInf
  | otherwise = Fin finite

propagateBounds :: MutableStore -> Rel -> LinExpr -> M ()
propagateBounds ms rel (LinExpr coefs k) = do
  let initial = adjustTotal 1 (Fin k) (Total 0 0 0)
  (minimumTotal, maximumTotal) <- liftIO $ foldM collect (initial, initial) (IM.toAscList coefs)
  require (totalBound minimumTotal <= Fin 0 && (rel /= RelEq || totalBound maximumTotal >= Fin 0))
  go minimumTotal maximumTotal (IM.toAscList coefs)
  where
    collect (mins,maxs) (v,coefficient) = do
      d <- getDomain ms v
      pure (adjustTotal 1 (minTerm coefficient d) mins, adjustTotal 1 (maxTerm coefficient d) maxs)
    go _ _ [] = pure ()
    go mins maxs ((v,coefficient):rest) = do
      old <- liftIO (getDomain ms v)
      let oldMin = minTerm coefficient old
          oldMax = maxTerm coefficient old
          restMin = totalBound (adjustTotal (-1) oldMin mins)
          restMax = totalBound (adjustTotal (-1) oldMax maxs)
          (lo,hi) = case rel of
            RelEq -> solveBounds coefficient (bNeg restMax) (bNeg restMin)
            _ -> solveBounds coefficient NegInf (bNeg restMin)
          d = intersectDomain old (Domain lo hi Set.empty)
          mins' = adjustTotal 1 (minTerm coefficient d) (adjustTotal (-1) oldMin mins)
          maxs' = adjustTotal 1 (maxTerm coefficient d) (adjustTotal (-1) oldMax maxs)
      require (not (domainEmpty d))
      when (d /= old) (liftIO (putDomain ms v d))
      go mins' maxs' rest

getDomain :: MutableStore -> VarId -> IO Domain
getDomain ms v = maybe fullDomain id <$> domainOf ms v

holds :: Rel -> Integer -> Bool
holds RelEq n = n == 0
holds RelNe n = n /= 0
holds RelLe n = n <= 0

normDomain :: Domain -> Domain
normDomain (Domain lo hi holes) =
  let lower = bumpLo lo
      upper = bumpHi hi
   in Domain lower upper (Set.filter (\n -> Fin n > lower && Fin n < upper) holes)
  where
    bumpLo (Fin n) | Set.member n holes = bumpLo (Fin (n+1))
    bumpLo b = b
    bumpHi (Fin n) | Set.member n holes = bumpHi (Fin (n-1))
    bumpHi b = b

domainEmpty :: Domain -> Bool
domainEmpty (Domain (Fin lo) (Fin hi) _) = lo > hi
domainEmpty _ = False

domainSingleton :: Domain -> Maybe Integer
domainSingleton (Domain (Fin lo) (Fin hi) _) | lo == hi = Just lo
domainSingleton _ = Nothing

domainMember :: Integer -> Domain -> Bool
domainMember n (Domain lo hi holes) = Fin n >= lo && Fin n <= hi && not (Set.member n holes)

intersectDomain :: Domain -> Domain -> Domain
intersectDomain (Domain lo hi holes) (Domain lo' hi' holes') =
  normDomain (Domain (max lo lo') (min hi hi') (Set.union holes holes'))

bNeg :: Bound -> Bound
bNeg NegInf = PosInf
bNeg PosInf = NegInf
bNeg (Fin n) = Fin (negate n)

bMul :: Integer -> Bound -> Bound
bMul coefficient (Fin n) = Fin (coefficient*n)
bMul coefficient bound
  | coefficient == 0 = Fin 0
  | coefficient > 0 = bound
  | otherwise = bNeg bound

minTerm, maxTerm :: Integer -> Domain -> Bound
minTerm coefficient (Domain lo hi _) = bMul coefficient (if coefficient > 0 then lo else hi)
maxTerm coefficient (Domain lo hi _) = bMul coefficient (if coefficient > 0 then hi else lo)

solveBounds :: Integer -> Bound -> Bound -> (Bound, Bound)
solveBounds coefficient lower upper
  | coefficient > 0 = (ceilB lower, floorB upper)
  | otherwise = (ceilB upper, floorB lower)
  where
    ceilB (Fin n) = Fin (negate (negate n `div` coefficient))
    ceilB bound = if coefficient > 0 then bound else bNeg bound
    floorB (Fin n) = Fin (n `div` coefficient)
    floorB bound = if coefficient > 0 then bound else bNeg bound
