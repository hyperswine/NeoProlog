{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | A simple CLP(Z) constraint store: interval domains with holes, bounds
-- propagation for linear (in)equalities, residual non-linear constraints and
-- general term disequality (@!=@).
--
-- The store also owns the substitution so that binding a constrained variable
-- can re-run propagation.
module Infera.CLP
  ( -- * Domains
    Bound (..),
    Domain (..),
    fullDomain,
    domainSize,
    domainValues,
    showDomain,

    -- * Constraints
    Rel (..),
    LinExpr (..),
    Constraint (..),
    constraintVars,
    constraintTerm,
    linearize,

    -- * Store
    Store (..),
    emptyStore,
    storeUnify,
    applyBindings,
    storeBind,
    addRelation,
    addDiseq,
    addDomain,
    addDomains,
    addAllDifferent,
    addReified,
    propagate,
    isConstrained,
    domainOf,
    storeWalk,
  )
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.List (foldl')
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Infera.Arith
import Infera.Error
import Infera.Syntax
import Infera.Unify

-- ─── DOMAINS ─────────────────────────────────────────────────────────────────

data Bound = NegInf | Fin !Integer | PosInf
  deriving (Eq, Ord, Show)

data Domain = Domain
  { domLo :: !Bound,
    domHi :: !Bound,
    domHoles :: !(Set Integer)
  }
  deriving (Eq, Show)

fullDomain :: Domain
fullDomain = Domain NegInf PosInf Set.empty

-- | Normalise: drop holes outside the interval and shrink the interval past
-- holes at either end.
normDomain :: Domain -> Domain
normDomain (Domain lo hi holes) =
  let lo' = bumpLo lo
      hi' = bumpHi hi
      holes' = Set.filter (\h -> Fin h > lo' && Fin h < hi') holes
   in Domain lo' hi' holes'
  where
    bumpLo (Fin x) | Set.member x holes = bumpLo (Fin (x + 1))
    bumpLo b = b
    bumpHi (Fin x) | Set.member x holes = bumpHi (Fin (x - 1))
    bumpHi b = b

domainEmpty :: Domain -> Bool
domainEmpty (Domain (Fin lo) (Fin hi) _) = lo > hi
domainEmpty _ = False

domainSingleton :: Domain -> Maybe Integer
domainSingleton (Domain (Fin lo) (Fin hi) _) | lo == hi = Just lo
domainSingleton _ = Nothing

domainSize :: Domain -> Maybe Integer
domainSize (Domain (Fin lo) (Fin hi) holes) = Just (hi - lo + 1 - fromIntegral (Set.size holes))
domainSize _ = Nothing

-- | Enumerate a finite domain in ascending order.
domainValues :: Domain -> Maybe [Integer]
domainValues (Domain (Fin lo) (Fin hi) holes) = Just [x | x <- [lo .. hi], not (Set.member x holes)]
domainValues _ = Nothing

domainMember :: Integer -> Domain -> Bool
domainMember x (Domain lo hi holes) = Fin x >= lo && Fin x <= hi && not (Set.member x holes)

intersectDomain :: Domain -> Domain -> Domain
intersectDomain (Domain l1 h1 s1) (Domain l2 h2 s2) =
  normDomain (Domain (max l1 l2) (min h1 h2) (Set.union s1 s2))

showBound :: Bound -> String
showBound NegInf = "inf"
showBound PosInf = "sup"
showBound (Fin n) = show n

showDomain :: Domain -> String
showDomain (Domain lo hi holes)
  | Set.null holes = showBound lo ++ ".." ++ showBound hi
  | otherwise = go lo (Set.toAscList holes)
  where
    go l [] = seg l hi
    go l (h : hs) = seg l (Fin (h - 1)) ++ " \\/ " ++ go (Fin (h + 1)) hs
    seg a b
      | a == b = showBound a
      | otherwise = showBound a ++ ".." ++ showBound b

-- ─── BOUND ARITHMETIC ────────────────────────────────────────────────────────

bAdd :: Bound -> Bound -> Bound
bAdd (Fin a) (Fin b) = Fin (a + b)
bAdd NegInf PosInf = NegInf -- should not occur; be conservative
bAdd PosInf NegInf = NegInf
bAdd NegInf _ = NegInf
bAdd _ NegInf = NegInf
bAdd PosInf _ = PosInf
bAdd _ PosInf = PosInf

bNeg :: Bound -> Bound
bNeg NegInf = PosInf
bNeg PosInf = NegInf
bNeg (Fin a) = Fin (negate a)

bMul :: Integer -> Bound -> Bound
bMul c (Fin x) = Fin (c * x)
bMul c b
  | c == 0 = Fin 0
  | c > 0 = b
  | otherwise = bNeg b

ceilDiv :: Integer -> Integer -> Integer
ceilDiv x c = negate (negate x `div` c)

floorDiv :: Integer -> Integer -> Integer
floorDiv = div

-- | Bounds on @x@ given @L <= c*x <= U@ (c non-zero).
solveBounds :: Integer -> Bound -> Bound -> (Bound, Bound)
solveBounds c l u
  | c > 0 = (ceilB l, floorB u)
  | otherwise = (ceilB u, floorB l)
  where
    ceilB (Fin x) = Fin (ceilDiv x c)
    ceilB b = if c > 0 then b else bNeg b
    floorB (Fin x) = Fin (floorDiv x c)
    floorB b = if c > 0 then b else bNeg b

-- ─── CONSTRAINTS ─────────────────────────────────────────────────────────────

-- | Relation of a linear expression to zero.
data Rel = RelEq | RelNe | RelLe
  deriving (Eq, Show)

data LinExpr = LinExpr
  { leCoefs :: !(IntMap Integer),
    leConst :: !Integer
  }
  deriving (Eq, Show)

data Constraint
  = -- | @expr rel 0@
    CLinear !Rel !LinExpr
  | -- | @lhs rel rhs@, not (yet) linear
    CNonLinear !Rel Term Term
  | -- | general disequality of terms
    CDiseq Term Term
  | -- | Integer expressions whose values must be pairwise different.
    CAllDifferent [Term]
  | -- | A Boolean truth value for an integer relation.
    CReified !Rel Term Term Term
  deriving (Eq, Show)

constraintVars :: Constraint -> [VarId]
constraintVars (CLinear _ le) = IM.keys (leCoefs le)
constraintVars (CNonLinear _ a b) = termVars a ++ termVars b
constraintVars (CDiseq a b) = termVars a ++ termVars b
constraintVars (CAllDifferent ts) = concatMap termVars ts
constraintVars (CReified _ a b truth) = termVars a ++ termVars b ++ termVars truth

relName :: Rel -> String
relName RelEq = "int_eq"
relName RelNe = "fd_ne"
relName RelLe = "fd_le"

-- | Render a constraint back into a term (for answers).
constraintTerm :: Constraint -> Term
constraintTerm (CNonLinear rel a b) = Compound (relName rel) [a, b]
constraintTerm (CDiseq a b) = Compound "neq" [a, b]
constraintTerm (CAllDifferent ts) = Compound "all_different" [mkList ts Nothing]
constraintTerm (CReified rel a b truth) = Compound "reify" [Compound (relName rel) [a, b], truth]
constraintTerm (CLinear rel (LinExpr coefs k)) =
  let terms = [t | t@(_, c) <- IM.toList coefs, c > 0] ++ [t | t@(_, c) <- IM.toList coefs, c < 0]
      lhs = build terms
   in Compound (relName rel) [lhs, IntLit (negate k)]
  where
    build [] = IntLit 0
    build ((v, c) : rest) = foldl' step (single v c) rest
    step acc (v, c)
      | c < 0 = Compound "minus" [acc, scaled v (negate c)]
      | otherwise = Compound "plus" [acc, scaled v c]
    single v c
      | c < 0 = Compound "minus" [IntLit 0, scaled v (negate c)]
      | otherwise = scaled v c
    scaled v 1 = Var v
    scaled v c = Compound "mul" [IntLit c, Var v]

-- | Linearise an integer expression under a substitution.  Fails (Nothing)
-- when the expression is non-linear in unbound variables or contains a
-- non-integer.
linearize :: Subst -> Term -> Maybe LinExpr
linearize s t = case walk s t of
  IntLit n -> Just (LinExpr IM.empty n)
  Var v -> Just (LinExpr (IM.singleton v 1) 0)
  Compound "plus" [a, b] -> addL <$> linearize s a <*> linearize s b
  Compound "minus" [a, b] -> addL <$> linearize s a <*> (scaleL (-1) <$> linearize s b)
  Compound "neg" [a] -> scaleL (-1) <$> linearize s a
  Compound "mul" [a, b] -> do
    la <- linearize s a
    lb <- linearize s b
    case (IM.null (leCoefs la), IM.null (leCoefs lb)) of
      (True, _) -> Just (scaleL (leConst la) lb)
      (_, True) -> Just (scaleL (leConst lb) la)
      _ -> Nothing
  other -> case evalIntExpr s other of
    Right (Just n) -> Just (LinExpr IM.empty n)
    _ -> Nothing

addL :: LinExpr -> LinExpr -> LinExpr
addL (LinExpr c1 k1) (LinExpr c2 k2) =
  LinExpr (IM.filter (/= 0) (IM.unionWith (+) c1 c2)) (k1 + k2)

scaleL :: Integer -> LinExpr -> LinExpr
scaleL 0 _ = LinExpr IM.empty 0
scaleL k (LinExpr c n) = LinExpr (IM.map (* k) c) (k * n)

-- ─── STORE ───────────────────────────────────────────────────────────────────

data Store = Store
  { stSubst :: !Subst,
    stDomains :: !(IntMap Domain),
    -- | Ordered residual constraints. Call 'propagate' after changing this
    -- field directly, so that its dependency index is rebuilt.
    stConstraints :: ![Constraint],
    -- | Superset of the variables mentioned by domains and constraints.
    stWatched :: !IntSet,
    stConstraintMap :: !(IntMap Constraint),
    stDependencies :: !(IntMap IntSet),
    stPending :: !IntSet,
    stDirtyVars :: !IntSet,
    stNextConstraint :: !Int,
    stConstraintCount :: !Int
  }
  deriving (Eq, Show)

emptyStore :: Store
emptyStore = Store emptySubst IM.empty [] IS.empty IM.empty IM.empty IS.empty IS.empty 0 0

type Checked a = Either SolveError (Maybe a)

storeWalk :: Store -> Term -> Term
storeWalk st = deepWalk (stSubst st)

isConstrained :: Store -> VarId -> Bool
isConstrained st v = IS.member v (stWatched st)

domainOf :: Store -> VarId -> Maybe Domain
domainOf st v = IM.lookup v (stDomains st)

watch :: [VarId] -> Store -> Store
watch vs st = st {stWatched = foldl' (flip IS.insert) (stWatched st) vs}

markDirty :: [VarId] -> Store -> Store
markDirty vs st = watch vs st {stDirtyVars = foldl' (flip IS.insert) (stDirtyVars st) vs}

putDomain :: VarId -> Domain -> Store -> Store
putDomain v d st
  | IM.lookup v (stDomains st) == Just d = st
  | otherwise = markDirty [v] st {stDomains = IM.insert v d (stDomains st)}

removeDomain :: VarId -> Store -> Store
removeDomain v st = markDirty [v] st {stDomains = IM.delete v (stDomains st)}

constraintIds :: Constraint -> IntSet
constraintIds = IS.fromList . constraintVars

register :: Int -> Constraint -> Store -> Store
register cid c st = watch (IS.toList vs) st
  { stConstraintMap = IM.insert cid c (stConstraintMap st),
    stDependencies = IS.foldl' (\deps v -> IM.insertWith IS.union v (IS.singleton cid) deps) (stDependencies st) vs,
    stConstraintCount = stConstraintCount st + 1
  }
  where
    vs = constraintIds c

unregister :: Int -> Constraint -> Store -> Store
unregister cid c st = st
  { stConstraintMap = IM.delete cid (stConstraintMap st),
    stDependencies = IS.foldl' (\deps v -> IM.update dropId v deps) (stDependencies st) (constraintIds c),
    stConstraintCount = stConstraintCount st - 1
  }
  where
    dropId ids = let ids' = IS.delete cid ids in if IS.null ids' then Nothing else Just ids'

post :: Constraint -> Store -> Store
post c st = register cid c st
  { stNextConstraint = cid + 1,
    stPending = IS.insert cid (stPending st)
  }
  where
    cid = stNextConstraint st

-- | Unify two terms, waking only constraints that mention changed variables.
storeUnify :: Store -> Term -> Term -> Checked Store
storeUnify st a b = case unify (stSubst st) a b of
  Nothing -> Right Nothing
  Just (s', bound) ->
    let st' = st {stSubst = s'}
     in if any (isConstrained st) bound
          then runPropagation (markDirty bound st')
          else Right (Just st')

-- | Accept the actual reference writes from an external occurs-checked
-- unifier. The caller owns binding validity and atomic rollback; this entry
-- point preserves the persistent propagation index and wakes exactly the
-- same changed-variable dependencies as 'storeUnify'. It deliberately does
-- not execute a second unification or rebuild the constraint index.
applyBindings :: [(VarId, Term)] -> Store -> Checked Store
applyBindings changes st =
  let bound = map fst changes
      substitution = foldl' (\s (variable, term) -> IM.insert variable term s)
        (stSubst st) changes
      updated = st {stSubst = substitution}
   in if any (isConstrained st) bound
        then runPropagation (markDirty bound updated)
        else Right (Just updated)

-- | Bind a variable to an integer (used by labeling).
storeBind :: Store -> VarId -> Integer -> Checked Store
storeBind st v n = storeUnify st (Var v) (IntLit n)

relation :: Store -> Rel -> Term -> Term -> Constraint
relation st rel lhs rhs = case linearize (stSubst st) (Compound "minus" [lhs, rhs]) of
  Just le -> CLinear rel le
  Nothing -> CNonLinear rel (storeWalk st lhs) (storeWalk st rhs)

-- | Add @lhs rel rhs@ where the relation is over @lhs - rhs@.
addRelation :: Rel -> Term -> Term -> Store -> Checked Store
addRelation rel lhs rhs st = runPropagation (post (relation st rel lhs rhs) st)

addDiseq :: Term -> Term -> Store -> Checked Store
addDiseq a b st = runPropagation (post (CDiseq (storeWalk st a) (storeWalk st b)) st)

addAllDifferent :: [Term] -> Store -> Checked Store
addAllDifferent terms st
  | length ts <= 1 = Right (Just st)
  | all integerItem ts = runPropagation (post (CAllDifferent ts) st)
  | otherwise = foldChecked (\s (a, b) -> addRelation RelNe a b s) st pairs
  where
    ts = map (storeWalk st) terms
    integerItem (Var _) = True
    integerItem t = case evalIntExpr emptySubst t of
      Right (Just _) -> True
      _ -> False
    -- Unsupported or still-symbolic expression lists keep the original
    -- pairwise posting order, delayed errors, and residual representation.
    pairs = [(a, b) | (i, a) <- zip [0 :: Int ..] ts, b <- drop (i + 1) ts]

addReified :: Rel -> Term -> Term -> Term -> Store -> Checked Store
addReified rel a b truth st = runPropagation (post (CReified rel (storeWalk st a) (storeWalk st b) (storeWalk st truth)) st)

-- | Restrict one term to an interval.
addDomain :: Term -> Bound -> Bound -> Store -> Checked Store
addDomain t lo hi = addDomains [t] lo hi

-- | Post a whole list of initial domains together. Once constraints are
-- active, preserve sequential error/failure observations: narrowing an
-- earlier item can raise an arithmetic error before a later item fails.
addDomains :: [Term] -> Bound -> Bound -> Store -> Checked Store
addDomains ts lo hi = go ts
  where
    go [] st = runPropagation st
    go (t : rest) st | stConstraintCount st > 0 = do
      restricted <- restrictTerm t lo hi st
      case restricted of
        Nothing -> Right Nothing
        Just next -> do
          propagated <- runPropagation next
          maybe (Right Nothing) (go rest) propagated
    go (t : rest) st = case restrictTerm t lo hi st of
      Right Nothing -> Right Nothing
      Right (Just next) -> go rest next
      Left err -> do
        -- Earlier domains may already make the branch fail. Preserve that
        -- failure before reporting a malformed later list item.
        prefix <- runPropagation st
        case prefix of
          Nothing -> Right Nothing
          Just _ -> Left err

foldChecked :: (a -> b -> Checked a) -> a -> [b] -> Checked a
foldChecked _ acc [] = Right (Just acc)
foldChecked f acc (x : xs) = f acc x >>= maybe (Right Nothing) (\next -> foldChecked f next xs)

restrictTerm :: Term -> Bound -> Bound -> Store -> Checked Store
restrictTerm t lo hi st = case walk (stSubst st) t of
  IntLit n
    | domainMember n (normDomain (Domain lo hi Set.empty)) -> Right (Just st)
    | otherwise -> Right Nothing
  Var v ->
    let d0 = IM.findWithDefault fullDomain v (stDomains st)
        d = intersectDomain d0 (Domain lo hi Set.empty)
     in if domainEmpty d then Right Nothing else Right (Just (putDomain v d st))
  other -> Left (CLPTypeError other)

-- ─── PROPAGATION ─────────────────────────────────────────────────────────────

maxRounds :: Int
maxRounds = 500

-- | Rebuild the dependency index and propagate. Normal posting and binding
-- use the persisted index directly; this entry point also supports callers
-- that record-update the public residual constraints or domains.
propagate :: Store -> Checked Store
propagate st = runPropagation rebuilt
  where
    base = st {stConstraintMap = IM.empty, stDependencies = IM.empty, stPending = IS.empty, stNextConstraint = 0, stConstraintCount = 0}
    indexed = foldl' (flip post) base (reverse (stConstraints st))
    rebuilt = markDirty (IM.keys (stDomains st) ++ IM.keys (stSubst st)) indexed

runPropagation :: Store -> Checked Store
runPropagation st0 = loop budget st0
  where
    -- Retain the old bounded-propagation safety valve for inconsistent
    -- unbounded recurrences. Unprocessed constraints remain queued.
    budget = maxRounds * max 1 (stConstraintCount st0)
    finish st = st {stConstraints = map snd (IM.toDescList (stConstraintMap st))}
    loop remaining st = do
      settled <- settleDirty st
      case settled of
        Nothing -> Right Nothing
        Just ready -> case IS.maxView (stPending ready) of
          _ | remaining <= 0 -> Right (Just (finish ready))
          Nothing -> Right (Just (finish ready))
          Just (cid, pending) ->
            let next = ready {stPending = pending}
             in case IM.lookup cid (stConstraintMap next) of
                  Nothing -> loop remaining next
                  Just c -> do
                    result <- reduce next c
                    case result of
                      ReducedFail -> Right Nothing
                      ReducedOK outcome reduced ->
                        let without = unregister cid c reduced
                            updated = case outcome of
                              Drop -> without
                              Keep c' -> register cid c' without
                         in loop (remaining - 1) updated

-- Normalize aliases and bind singleton domains only for changed variables.
-- Wake the old dependency entries before moving domains to canonical roots:
-- constraints then rewrite their own dependency entries when reduced.
settleDirty :: Store -> Checked Store
settleDirty st
  | IS.null (stDirtyVars st) = Right (Just st)
  | otherwise = do
      let changed = stDirtyVars st
          pending = IS.foldl' (\ids v -> IS.union ids (IM.findWithDefault IS.empty v (stDependencies st))) (stPending st) changed
          ready = st {stDirtyVars = IS.empty, stPending = pending}
      result <- foldChecked settle ready (IS.toList changed)
      maybe (Right Nothing) settleDirty result
  where
    settle acc v = case IM.lookup v (stDomains acc) of
      Nothing -> Right (Just acc)
      Just d
        | domainEmpty d -> Right Nothing
        | otherwise -> case walk (stSubst acc) (Var v) of
            IntLit n
              | domainMember n d -> Right (Just (removeDomain v acc))
              | otherwise -> Right Nothing
            Var w
              | w /= v ->
                  let dw = IM.findWithDefault fullDomain w (stDomains acc)
                      d' = intersectDomain dw d
                   in if domainEmpty d'
                        then Right Nothing
                        else Right (Just (putDomain w d' (removeDomain v acc)))
              | Just n <- domainSingleton d ->
                  Right (Just (removeDomain v acc {stSubst = IM.insert v (IntLit n) (stSubst acc)}))
              | otherwise -> Right (Just acc)
            other -> Left (CLPTypeError other)

data Outcome = Keep Constraint | Drop

data Reduced = ReducedFail | ReducedOK Outcome Store

reduce :: Store -> Constraint -> Either SolveError Reduced
reduce st c = case c of
  CAllDifferent ts -> reduceAllDifferent st ts
  CReified rel a b truth -> reduceReified st rel a b truth
  CDiseq a b ->
    let a' = storeWalk st a
        b' = storeWalk st b
     in if a' == b'
          then Right ReducedFail
          else case unifyPlain (stSubst st) a' b' of
            Nothing -> Right (ReducedOK Drop st)
            Just _ -> Right (ReducedOK (Keep (CDiseq a' b')) st)
  CNonLinear rel a b ->
    case linearize (stSubst st) (Compound "minus" [a, b]) of
      Just le -> reduce (watch (IM.keys (leCoefs le)) st) (CLinear rel le)
      Nothing | rel == RelEq, Compound "abs" [expr] <- storeWalk st b -> reduceAbs st a expr
      Nothing | rel == RelEq, Compound "abs" [expr] <- storeWalk st a -> reduceAbs st b expr
      Nothing ->
        let a' = storeWalk st a
            b' = storeWalk st b
         in if isGroundTerm a' && isGroundTerm b'
              then do
                ma <- evalIntExpr emptySubst a'
                mb <- evalIntExpr emptySubst b'
                case (ma, mb) of
                  (Just x, Just y) ->
                    Right (if holds rel (x - y) then ReducedOK Drop st else ReducedFail)
                  _ -> Right (ReducedOK (Keep (CNonLinear rel a' b')) st)
              else Right (ReducedOK (Keep (CNonLinear rel a' b')) st)
  CLinear rel le -> do
    le' <- substituteLin st le
    let coefs = leCoefs le'
        k = leConst le'
    if IM.null coefs
      then Right (if holds rel k then ReducedOK Drop st else ReducedFail)
      else case rel of
        RelNe
          | [(v, cv)] <- IM.toList coefs ->
              if negate k `mod` cv == 0
                 then
                   let hole = negate k `div` cv
                       d0 = IM.findWithDefault fullDomain v (stDomains st)
                       d = normDomain d0 {domHoles = Set.insert hole (domHoles d0)}
                    in if domainEmpty d
                         then Right ReducedFail
                         else Right (ReducedOK Drop (putDomain v d st))
                 else Right (ReducedOK Drop st)
          | otherwise -> Right (ReducedOK (Keep (CLinear rel le')) st)
        _ -> case propagateBounds st rel le' of
          Nothing -> Right ReducedFail
          Just st'
            -- a single-variable bound is fully captured by the domain
            | IM.size coefs == 1 -> Right (ReducedOK Drop st')
            | otherwise -> Right (ReducedOK (Keep (CLinear rel le')) st')

holds :: Rel -> Integer -> Bool
holds RelEq x = x == 0
holds RelNe x = x /= 0
holds RelLe x = x <= 0

-- Fold bound variables into the constant and re-map aliased variables.
substituteLin :: Store -> LinExpr -> Either SolveError LinExpr
substituteLin st (LinExpr coefs k0) = go (IM.toList coefs) IM.empty k0
  where
    go [] acc k = Right (LinExpr (IM.filter (/= 0) acc) k)
    go ((v, c) : rest) acc k = case walk (stSubst st) (Var v) of
      IntLit n -> go rest acc (k + c * n)
      Var w -> go rest (IM.insertWith (+) w c acc) k
      other -> Left (CLPTypeError other)

-- A removable aggregate makes each coefficient visit constant-time. Keeping
-- infinity counts avoids unsafe subtraction of infinite interval bounds.
data Total = Total !Integer !Int !Int

emptyTotal :: Total
emptyTotal = Total 0 0 0

adjustTotal :: Int -> Bound -> Total -> Total
adjustTotal delta b (Total finite neg pos) = case b of
  Fin n -> Total (finite + fromIntegral delta * n) neg pos
  NegInf -> Total finite (neg + delta) pos
  PosInf -> Total finite neg (pos + delta)

totalBound :: Total -> Bound
totalBound (Total finite neg pos)
  | neg > 0 = NegInf
  | pos > 0 = PosInf
  | otherwise = Fin finite

minTerm :: Integer -> Domain -> Bound
minTerm c (Domain lo hi _) = if c > 0 then bMul c lo else bMul c hi

maxTerm :: Integer -> Domain -> Bound
maxTerm c (Domain lo hi _) = if c > 0 then bMul c hi else bMul c lo

getDomain :: Store -> VarId -> Domain
getDomain st v = IM.findWithDefault fullDomain v (stDomains st)

linearBounds :: Store -> LinExpr -> (Bound, Bound)
linearBounds st (LinExpr coefs k) = IM.foldlWithKey' step (Fin k, Fin k) coefs
  where
    step (lo, hi) v cv = let d = getDomain st v in (bAdd lo (minTerm cv d), bAdd hi (maxTerm cv d))

-- | Bounds propagation in O(k) coefficient visits rather than rescanning all
-- other coefficients for each variable. Update the aggregate after each
-- narrowing to retain the previous ordered, within-pass propagation strength.
propagateBounds :: Store -> Rel -> LinExpr -> Maybe Store
propagateBounds st0 rel (LinExpr coefs k)
  | impossible = Nothing
  | otherwise = go st0 minTotal maxTotal (IM.toList coefs)
  where
    (minTotal, maxTotal) = IM.foldlWithKey' collect (adjustTotal 1 (Fin k) emptyTotal, adjustTotal 1 (Fin k) emptyTotal) coefs
    collect (mins, maxs) v cv = let d = getDomain st0 v in (adjustTotal 1 (minTerm cv d) mins, adjustTotal 1 (maxTerm cv d) maxs)
    impossible = totalBound minTotal > Fin 0 || (rel == RelEq && totalBound maxTotal < Fin 0)
    go st _ _ [] = Just st
    go st mins maxs ((v, cv) : rest) =
      let d0 = getDomain st v
          oldMin = minTerm cv d0
          oldMax = maxTerm cv d0
          restMin = totalBound (adjustTotal (-1) oldMin mins)
          restMax = totalBound (adjustTotal (-1) oldMax maxs)
          (lo, hi) = case rel of
            RelEq -> solveBounds cv (bNeg restMax) (bNeg restMin)
            _ -> solveBounds cv NegInf (bNeg restMin)
          d = intersectDomain d0 (Domain lo hi Set.empty)
          mins' = adjustTotal 1 (minTerm cv d) (adjustTotal (-1) oldMin mins)
          maxs' = adjustTotal 1 (maxTerm cv d) (adjustTotal (-1) oldMax maxs)
       in if domainEmpty d
            then Nothing
            else go (if d == d0 then st else putDomain v d st) mins' maxs' rest

-- ─── REIFIED RELATIONS AND ABSOLUTE VALUES ──────────────────────────────────

reduceReified :: Store -> Rel -> Term -> Term -> Term -> Either SolveError Reduced
reduceReified st rel a b truth = do
  restricted <- restrictTerm truth (Fin 0) (Fin 1) st
  case restricted of
    Nothing -> Right ReducedFail
    Just st' -> do
      let a' = storeWalk st' a
          b' = storeWalk st' b
          truth' = storeWalk st' truth
          ordinary = relation st' rel a' b'
      known <- relationTruth st' ordinary
      case truth' of
        IntLit flag ->
          case known of
            Just yes | yes /= (flag == 1) -> Right ReducedFail
            Just _ -> Right (ReducedOK Drop st')
            Nothing -> reduce st' (if flag == 1 then ordinary else opposite ordinary)
        Var _ -> case known of
          Nothing -> Right (ReducedOK (Keep (CReified rel a' b' truth')) st')
          Just yes -> do
            result <- restrictTerm truth' (Fin (if yes then 1 else 0)) (Fin (if yes then 1 else 0)) st'
            Right (maybe ReducedFail (ReducedOK Drop) result)
        _ -> Left (CLPTypeError truth')
  where
    opposite (CLinear RelEq le) = CLinear RelNe le
    opposite (CLinear RelNe le) = CLinear RelEq le
    opposite (CLinear RelLe le) = CLinear RelLe (addL (scaleL (-1) le) (LinExpr IM.empty 1))
    opposite (CNonLinear RelEq x y) = CNonLinear RelNe x y
    opposite (CNonLinear RelNe x y) = CNonLinear RelEq x y
    opposite (CNonLinear RelLe x y) = CNonLinear RelLe (Compound "plus" [y, IntLit 1]) x
    opposite other = other

relationTruth :: Store -> Constraint -> Either SolveError (Maybe Bool)
relationTruth st (CLinear rel le) = do
  le' <- substituteLin st le
  let (lo, hi) = linearBounds st le'
      equality
        | lo > Fin 0 || hi < Fin 0 = Just False
        | lo == Fin 0 && hi == Fin 0 = Just True
        | [(_, cv)] <- IM.toList (leCoefs le'), negate (leConst le') `mod` cv /= 0 = Just False
        | [(v, cv)] <- IM.toList (leCoefs le'), not (domainMember (negate (leConst le') `div` cv) (getDomain st v)) = Just False
        | otherwise = Nothing
  Right $ case rel of
    RelEq -> equality
    RelNe -> not <$> equality
    RelLe
      | hi <= Fin 0 -> Just True
      | lo > Fin 0 -> Just False
      | otherwise -> Nothing
relationTruth st (CNonLinear rel a b) = do
  ma <- evalIntExpr (stSubst st) a
  mb <- evalIntExpr (stSubst st) b
  Right (holds rel <$> ((-) <$> ma <*> mb))
relationTruth _ _ = Right Nothing

-- Propagate the convex bounds of Result = abs(Expression). Once the sign is
-- fixed the remaining relation is linear. Before then a single-variable
-- expression can also exclude the forbidden central interval.
reduceAbs :: Store -> Term -> Term -> Either SolveError Reduced
reduceAbs st result expr =
  case (linearize (stSubst st) result, linearize (stSubst st) expr) of
    (Just lr, Just le)
      | retainsVariables result lr && retainsVariables expr le ->
        let (elo, ehi) = linearBounds st le
            alo | elo >= Fin 0 = elo
                | ehi <= Fin 0 = bNeg ehi
                | otherwise = Fin 0
            ahi = max (absBound elo) (absBound ehi)
            bounded = constrainBounds st lr alo ahi >>= \s ->
              let (_, rhi) = linearBounds s lr
               in constrainBounds s le (bNeg rhi) rhi
         in case bounded of
              Nothing -> Right ReducedFail
              Just st' ->
                let (rlo, _) = linearBounds st' lr
                    (lo, hi) = linearBounds st' le
                 in if lo >= Fin 0
                      then reduce st' (CLinear RelEq (addL lr (scaleL (-1) le)))
                      else if hi <= Fin 0
                        then reduce st' (CLinear RelEq (addL lr le))
                        else case excludeAbsInterior st' le rlo of
                          Nothing -> Right ReducedFail
                          Just st'' -> Right (ReducedOK (Keep (CNonLinear RelEq (storeWalk st'' result) (Compound "abs" [storeWalk st'' expr]))) st'')
    _ ->
      let result' = storeWalk st result
          expr' = storeWalk st expr
          residual = ReducedOK (Keep (CNonLinear RelEq result' (Compound "abs" [expr']))) st
       -- Match the ordinary nonlinear relation's delayed error behavior:
       -- an invalid ground operand is evaluated only once both sides are
       -- ground. A subsequent failing goal can discard the residual first.
       in if isGroundTerm result' && isGroundTerm expr'
            then do
              mr <- evalIntExpr emptySubst result'
              me <- evalIntExpr emptySubst expr'
              case (mr, me) of
                (Just r, Just e) -> Right (if r == abs e then ReducedOK Drop st else ReducedFail)
                _ -> Right residual
            else Right residual
  where
    -- Unlike an already-linear relation, abs was previously a nonlinear
    -- residual that validated every inner arithmetic operand when ground.
    -- Cancellation (X-X or 0*X) must not erase that validation obligation.
    retainsVariables t le = all (\v -> IM.member v (leCoefs le)) (termVars (storeWalk st t))
    absBound (Fin n) = Fin (abs n)
    absBound _ = PosInf

constrainBounds :: Store -> LinExpr -> Bound -> Bound -> Maybe Store
constrainBounds st le lo hi = lower >>= upper
  where
    lower = case lo of
      Fin n -> propagateBounds st RelLe (addL (scaleL (-1) le) (LinExpr IM.empty n))
      _ -> Just st
    upper s = case hi of
      Fin n -> propagateBounds s RelLe (addL le (LinExpr IM.empty (negate n)))
      _ -> Just s

excludeAbsInterior :: Store -> LinExpr -> Bound -> Maybe Store
excludeAbsInterior st (LinExpr coefs k) (Fin lower)
  | lower > 0, [(v, cv)] <- IM.toList coefs =
      case solveBounds cv (Fin (1 - lower - k)) (Fin (lower - 1 - k)) of
        (Fin lo, Fin hi) -> excludeInterval st v lo hi
        _ -> Just st
excludeAbsInterior st _ _ = Just st

excludeInterval :: Store -> VarId -> Integer -> Integer -> Maybe Store
excludeInterval st v lo hi
  | lo > hi = Just st
  | otherwise =
      let d0 = getDomain st v
          d
            | Fin lo <= domLo d0 = intersectDomain d0 (Domain (Fin (hi + 1)) PosInf Set.empty)
            | Fin hi >= domHi d0 = intersectDomain d0 (Domain NegInf (Fin (lo - 1)) Set.empty)
            | hi - lo <= 4096 = normDomain d0 {domHoles = Set.union (Set.fromList [lo .. hi]) (domHoles d0)}
            | otherwise = d0
       in if domainEmpty d then Nothing else Just (if d == d0 then st else putDomain v d st)

-- ─── GLOBAL ALL-DIFFERENT ───────────────────────────────────────────────────

reduceAllDifferent :: Store -> [Term] -> Either SolveError Reduced
reduceAllDifferent st terms | length terms <= 1 = Right (ReducedOK Drop st)
reduceAllDifferent st terms = do
  let ts = map (storeWalk st) terms
      classified = map classify ts
  case sequence classified of
    Nothing -> fallback st ts
    Just values ->
      let fixedValues = [n | Right n <- values]
          fixed = Set.fromList fixedValues
          vars = [v | Left v <- values]
       in if IS.size (IS.fromList vars) /= length vars || Set.size fixed /= length fixedValues
            then Right ReducedFail
            else case removeFixed fixed st vars >>= hallIntervals vars >>= matchingPrune vars of
              Nothing -> Right ReducedFail
              Just st' -> Right (ReducedOK (if null vars then Drop else Keep (CAllDifferent ts)) st')
  where
    -- Preserve arithmetic-expression support of the old pairwise definition.
    classify (Var v) = Just (Left v)
    classify t = case evalIntExpr emptySubst t of
      Right (Just n) -> Just (Right n)
      _ -> Nothing
    -- A manually supplied global constraint may contain symbolic expressions.
    -- Replace its wrapper with persistent pair constraints, retaining each
    -- pair's nonlinear residual or linear integer-validation obligation.
    fallback acc ts = Right (ReducedOK Drop (foldl' addPair acc pairs))
      where
        pairs = [(a, b) | (i, a) <- zip [0 :: Int ..] ts, b <- drop (i + 1) ts]
        addPair s (a, b) = post (relation s RelNe a b) s

removeFixed :: Set Integer -> Store -> [VarId] -> Maybe Store
removeFixed fixed = foldMaybe step
  where
    step st v =
      let d0 = getDomain st v
          d = normDomain d0 {domHoles = Set.union fixed (domHoles d0)}
       -- Even without fixed values, a native integer all-different establishes
       -- integer variables. A later structural binding must raise the same
       -- CLP type error as the old linear pairwise inequalities.
       in if domainEmpty d then Nothing else Just (putDomain v d st)

foldMaybe :: (a -> b -> Maybe a) -> a -> [b] -> Maybe a
foldMaybe _ acc [] = Just acc
foldMaybe f acc (x : xs) = f acc x >>= \next -> foldMaybe f next xs

-- Hall intervals reserve a tight interval for variables wholly inside it.
-- Bound the cubic endpoint search; larger collections still receive fixed
-- value filtering and the matching feasibility check below.
hallIntervals :: [VarId] -> Store -> Maybe Store
hallIntervals vars st
  | length vars > 48 = Just st
  | otherwise = foldMaybe prune st intervals
  where
    lows = Set.toAscList (Set.fromList [lo | v <- vars, Fin lo <- [domLo (getDomain st v)]])
    highs = Set.toAscList (Set.fromList [hi | v <- vars, Fin hi <- [domHi (getDomain st v)]])
    intervals = [(lo, hi) | lo <- lows, hi <- highs, lo <= hi, hi - lo < fromIntegral (length vars)]
    prune s (lo, hi) =
      let inside v = let d = getDomain s v in domLo d >= Fin lo && domHi d <= Fin hi
          reserved = filter inside vars
          capacity = hi - lo + 1
       in case compare (fromIntegral (length reserved)) capacity of
            GT -> Nothing
            LT -> Just s
            EQ -> foldMaybe (\acc v -> if inside v then Just acc else excludeInterval acc v lo hi) s vars

-- Matching detects Hall sets involving holes as well as contiguous intervals.
-- Small domains additionally remove each unsupported edge. These budgets are
-- about propagation cost, never about satisfiability or the allowed answers.
matchingPrune :: [VarId] -> Store -> Maybe Store
matchingPrune vars st = case finiteChoices of
  Nothing -> Just st
  Just choices
    | not (perfectMatching choices) -> Nothing
    | length vars <= 16 && edgeCount <= 128 -> foldMaybe prune st choices
    | otherwise -> Just st
    where
      edgeCount = sum (map (length . snd) choices)
      prune s (v, vals) =
        let unsupported = [n | n <- vals, not (perfectMatching [(w, if w == v then [n] else filter (/= n) ws) | (w, ws) <- choices])]
            d0 = getDomain s v
            d = normDomain d0 {domHoles = Set.union (Set.fromList unsupported) (domHoles d0)}
         in if domainEmpty d then Nothing else Just (if d == d0 then s else putDomain v d s)
  where
    finiteChoices
      | length vars > 64 = Nothing
      | otherwise = do
          sizes <- traverse (domainSize . getDomain st) vars
          if sum sizes > 512
            then Nothing
            else traverse (\v -> (,) v <$> domainValues (getDomain st v)) vars

perfectMatching :: [(VarId, [Integer])] -> Bool
perfectMatching choices = maybe False (const True) (foldMaybe add Map.empty choices)
  where
    domains = IM.fromList choices
    add matching (v, _) = augment v Set.empty matching
    augment v seen matching = try (IM.findWithDefault [] v domains)
      where
        try [] = Nothing
        try (n : ns)
          | Set.member n seen = try ns
          | otherwise = case Map.lookup n matching of
              Nothing -> Just (Map.insert n v matching)
              Just previous -> case augment previous (Set.insert n seen) matching of
                Just rerouted -> Just (Map.insert n v rerouted)
                Nothing -> try ns
