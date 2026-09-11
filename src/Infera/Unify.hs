-- | Substitutions, unification and variable renaming.
module Infera.Unify
  ( Subst,
    emptySubst,
    walk,
    deepWalk,
    occurs,
    unify,
    unifyPlain,
    termVars,
    isGround,
    isGroundTerm,
    renameTerm,
    renameBody,
    replaceCuts,
    canonicalize,
    instantiate,
  )
where

import Control.Monad (foldM)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.List (nub)
import Infera.Syntax

type Subst = IntMap Term

emptySubst :: Subst
emptySubst = IM.empty

-- | Dereference the top of a term.
walk :: Subst -> Term -> Term
walk s (Var v) = case IM.lookup v s of
  Just t -> walk s t
  Nothing -> Var v
walk _ t = t

-- | Fully dereference a term.
deepWalk :: Subst -> Term -> Term
deepWalk s t = case walk s t of
  Compound f as -> Compound f (map (deepWalk s) as)
  t' -> t'

occurs :: Subst -> VarId -> Term -> Bool
occurs s v t = case walk s t of
  Var v' -> v == v'
  Compound _ as -> any (occurs s v) as
  _ -> False

-- | Unify two terms.  Returns the extended substitution together with the
-- variables that were bound in the process (used to trigger constraint
-- propagation).
unify :: Subst -> Term -> Term -> Maybe (Subst, [VarId])
unify s0 a0 b0 = go (s0, []) a0 b0
  where
    go (s, bound) a b = case (walk s a, walk s b) of
      (Var v, Var w)
        | v == w -> Just (s, bound)
        | v > w -> Just (IM.insert v (Var w) s, v : bound)
        | otherwise -> Just (IM.insert w (Var v) s, w : bound)
      (Var v, t)
        | occurs s v t -> Nothing
        | otherwise -> Just (IM.insert v t s, v : bound)
      (t, Var v)
        | occurs s v t -> Nothing
        | otherwise -> Just (IM.insert v t s, v : bound)
      (Atom x, Atom y) | x == y -> Just (s, bound)
      (IntLit x, IntLit y) | x == y -> Just (s, bound)
      (FloatLit x, FloatLit y) | x == y -> Just (s, bound)
      (CharLit x, CharLit y) | x == y -> Just (s, bound)
      (StrLit x, StrLit y) | x == y -> Just (s, bound)
      (Compound f xs, Compound g ys)
        | f == g && length xs == length ys ->
            foldM (\acc (x, y) -> go acc x y) (s, bound) (zip xs ys)
      _ -> Nothing

unifyPlain :: Subst -> Term -> Term -> Maybe Subst
unifyPlain s a b = fst <$> unify s a b

-- | Distinct variables of a term in order of first occurrence.
termVars :: Term -> [VarId]
termVars = nub . termVarIds

isGround :: Subst -> Term -> Bool
isGround s t = case walk s t of
  Var _ -> False
  Compound _ as -> all (isGround s) as
  _ -> True

isGroundTerm :: Term -> Bool
isGroundTerm (Var _) = False
isGroundTerm (Compound _ as) = all isGroundTerm as
isGroundTerm _ = True

-- | Shift every variable id by an offset (renaming a clause apart).
renameTerm :: Int -> Term -> Term
renameTerm off (Var v) = Var (v + off)
renameTerm off (Compound f as) = Compound f (map (renameTerm off) as)
renameTerm _ t = t

-- | Rename a clause body goal, replacing bare cuts with a cut that refers to
-- the barrier @off@ (the activation's base id, unique per activation).
renameBody :: Int -> Term -> Term
renameBody off = go
  where
    go (Var v) = Var (v + off)
    go (Atom "!") = Compound "$cut" [IntLit (fromIntegral off)]
    go (Compound f as) = Compound f (map go as)
    go t = t

-- | Replace bare cuts with cuts owned by the given barrier (no renaming).
replaceCuts :: Int -> Term -> Term
replaceCuts b = go
  where
    go (Atom "!") = Compound "$cut" [IntLit (fromIntegral b)]
    go (Compound f as) = Compound f (map go as)
    go t = t

-- | Fully dereference a term and renumber its free variables @0, 1, ...@ in
-- order of first occurrence.  Returns the canonical term and the original
-- variable ids in canonical order.
canonicalize :: Subst -> Term -> (Term, [VarId])
canonicalize s t0 =
  let t = deepWalk s t0
      vs = termVars t
      m = IM.fromList (zip vs [0 ..])
   in (relabel m t, vs)
  where
    relabel m (Var v) = Var (IM.findWithDefault v v m)
    relabel m (Compound f as) = Compound f (map (relabel m) as)
    relabel _ u = u

-- | Instantiate a canonical term with fresh variables starting at @base@.
instantiate :: Int -> Term -> Term
instantiate = renameTerm
