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
    storeBind,
    addRelation,
    addDiseq,
    addDomain,
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
  deriving (Eq, Show)

constraintVars :: Constraint -> [VarId]
constraintVars (CLinear _ le) = IM.keys (leCoefs le)
constraintVars (CNonLinear _ a b) = termVars a ++ termVars b
constraintVars (CDiseq a b) = termVars a ++ termVars b

relName :: Rel -> String
relName RelEq = "int_eq"
relName RelNe = "fd_ne"
relName RelLe = "fd_le"

-- | Render a constraint back into a term (for answers).
constraintTerm :: Constraint -> Term
constraintTerm (CNonLinear rel a b) = Compound (relName rel) [a, b]
constraintTerm (CDiseq a b) = Compound "neq" [a, b]
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
    stConstraints :: ![Constraint],
    -- | Superset of the variables mentioned by domains and constraints.
    stWatched :: !IntSet
  }
  deriving (Eq, Show)

emptyStore :: Store
emptyStore = Store emptySubst IM.empty [] IS.empty

type Checked a = Either SolveError (Maybe a)

storeWalk :: Store -> Term -> Term
storeWalk st = deepWalk (stSubst st)

isConstrained :: Store -> VarId -> Bool
isConstrained st v = IS.member v (stWatched st)

domainOf :: Store -> VarId -> Maybe Domain
domainOf st v = IM.lookup v (stDomains st)

watch :: [VarId] -> Store -> Store
watch vs st = st {stWatched = foldl' (flip IS.insert) (stWatched st) vs}

-- | Unify two terms in the store, propagating constraints if a watched
-- variable was bound.
storeUnify :: Store -> Term -> Term -> Checked Store
storeUnify st a b = case unify (stSubst st) a b of
  Nothing -> Right Nothing
  Just (s', bound) ->
    let st' = st {stSubst = s'}
     in if any (isConstrained st) bound then propagate st' else Right (Just st')

-- | Bind a variable to an integer (used by labeling).
storeBind :: Store -> VarId -> Integer -> Checked Store
storeBind st v n = storeUnify st (Var v) (IntLit n)

-- | Add @lhs rel rhs@ where the relation is over @lhs - rhs@.
addRelation :: Rel -> Term -> Term -> Store -> Checked Store
addRelation rel lhs rhs st =
  let vs = termVars (storeWalk st lhs) ++ termVars (storeWalk st rhs)
      c = case linearize (stSubst st) (Compound "minus" [lhs, rhs]) of
        Just le -> CLinear rel le
        Nothing -> CNonLinear rel lhs rhs
   in propagate (watch vs st {stConstraints = c : stConstraints st})

addDiseq :: Term -> Term -> Store -> Checked Store
addDiseq a b st =
  let vs = termVars (storeWalk st a) ++ termVars (storeWalk st b)
   in propagate (watch vs st {stConstraints = CDiseq a b : stConstraints st})

-- | Restrict a term (a variable or an integer) to an interval.
addDomain :: Term -> Bound -> Bound -> Store -> Checked Store
addDomain t lo hi st = case walk (stSubst st) t of
  IntLit n
    | domainMember n (normDomain (Domain lo hi Set.empty)) -> Right (Just st)
    | otherwise -> Right Nothing
  Var v ->
    let d0 = IM.findWithDefault fullDomain v (stDomains st)
        d = intersectDomain d0 (Domain lo hi Set.empty)
     in propagate (watch [v] st {stDomains = IM.insert v d (stDomains st)})
  other -> Left (CLPTypeError other)

-- ─── PROPAGATION ─────────────────────────────────────────────────────────────

maxRounds :: Int
maxRounds = 500

-- | Run propagation to a fixpoint (bounded).
propagate :: Store -> Checked Store
propagate = loop 0
  where
    loop :: Int -> Store -> Checked Store
    loop n st0 = do
      r1 <- normaliseDomains st0
      case r1 of
        Nothing -> Right Nothing
        Just st1 -> do
          r2 <- reduceAll st1 [] (stConstraints st1)
          case r2 of
            Nothing -> Right Nothing
            Just (st2, kept) -> do
              r3 <- bindSingletons st2 {stConstraints = reverse kept}
              case r3 of
                Nothing -> Right Nothing
                Just st3 ->
                  if n >= maxRounds || quiescent st0 st3
                    then Right (Just st3)
                    else loop (n + 1) st3

    quiescent a b =
      IM.size (stSubst a) == IM.size (stSubst b)
        && stDomains a == stDomains b
        && length (stConstraints a) == length (stConstraints b)

    reduceAll st kept [] = Right (Just (st, kept))
    reduceAll st kept (c : cs) = do
      r <- reduce st c
      case r of
        ReducedFail -> Right Nothing
        ReducedOK Drop st' -> reduceAll st' kept cs
        ReducedOK (Keep c') st' -> reduceAll st' (c' : kept) cs

data Outcome = Keep Constraint | Drop

data Reduced = ReducedFail | ReducedOK Outcome Store

reduce :: Store -> Constraint -> Either SolveError Reduced
reduce st c = case c of
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
                         else Right (ReducedOK Drop (watch [v] st {stDomains = IM.insert v d (stDomains st)}))
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

-- Bounds propagation for @sum c_i x_i + k (= | <=) 0@.
propagateBounds :: Store -> Rel -> LinExpr -> Maybe Store
propagateBounds st0 rel (LinExpr coefs k) = foldlM' step st0 (IM.toList coefs)
  where
    foldlM' f z xs = foldl' (\acc x -> acc >>= \a -> f a x) (Just z) xs

    domOf st v = IM.findWithDefault fullDomain v (stDomains st)

    step st (v, cv) =
      let others = [(w, cw) | (w, cw) <- IM.toList coefs, w /= v]
          restMin = foldl' bAdd (Fin k) [minTerm cw (domOf st w) | (w, cw) <- others]
          restMax = foldl' bAdd (Fin k) [maxTerm cw (domOf st w) | (w, cw) <- others]
          (lo, hi) = case rel of
            RelEq -> solveBounds cv (bNeg restMax) (bNeg restMin)
            _ -> solveBounds cv NegInf (bNeg restMin)
          d0 = domOf st v
          d = intersectDomain d0 (Domain lo hi Set.empty)
       in if domainEmpty d
            then Nothing
            else
              if d == d0
                then Just st
                else Just st {stDomains = IM.insert v d (stDomains st)}

    minTerm c (Domain lo hi _) = if c > 0 then bMul c lo else bMul c hi
    maxTerm c (Domain lo hi _) = if c > 0 then bMul c hi else bMul c lo

-- Re-attach domains of variables that have been bound or aliased.
normaliseDomains :: Store -> Checked Store
normaliseDomains st0 = go (IM.toList (stDomains st0)) st0
  where
    go [] st = Right (Just st)
    go ((v, d) : rest) st = case walk (stSubst st) (Var v) of
      Var w
        | w == v -> go rest st
        | otherwise ->
            let dw = IM.findWithDefault fullDomain w (stDomains st)
                d' = intersectDomain dw d
             in if domainEmpty d'
                  then Right Nothing
                  else go rest (watch [w] st {stDomains = IM.insert w d' (IM.delete v (stDomains st))})
      IntLit n
        | domainMember n d -> go rest st {stDomains = IM.delete v (stDomains st)}
        | otherwise -> Right Nothing
      other -> Left (CLPTypeError other)

-- Bind variables whose domain collapsed to a single value.
bindSingletons :: Store -> Checked Store
bindSingletons st0 = go (IM.toList (stDomains st0)) st0
  where
    go [] st = Right (Just st)
    go ((v, d) : rest) st
      | domainEmpty d = Right Nothing
      | otherwise = case domainSingleton d of
          Just n -> case walk (stSubst st) (Var v) of
            Var w | w == v -> go rest st {stSubst = IM.insert v (IntLit n) (stSubst st), stDomains = IM.delete v (stDomains st)}
            _ -> go rest st
          Nothing -> go rest st
