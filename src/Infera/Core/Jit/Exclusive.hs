{-# LANGUAGE LambdaCase #-}

-- | Clause exclusivity for native code: whether committing to the first
-- clause whose head and guards hold can differ from the interpreter, which
-- would also try the later clauses. Shared by the shape kernels in
-- "Infera.Core.Jit" and the clause compiler in "Infera.Core.Jit.Clause".
module Infera.Core.Jit.Exclusive
  ( ArgPath,
    IntRange (..),
    Shape (..),
    shapeOf,
    shapesDisjoint,
    headsExclusive,
    clausesExclusive,
    clauseConstraints,
    exprConstraints,
    exprFacts,
    laterRaisesNothingNew,
    refineRange,
    flipCmp,
    isCmpOp,
  )
where

import qualified Data.Map.Strict as M
import qualified Infera.Syntax as S

-- | A position in the input arguments: argument index, then cons cell
-- offsets (1 for the head, 2 for the tail).
type ArgPath = (Int, [Int])

data Shape = ShNil | ShCons Shape Shape | ShInt Integer | ShAtom String | ShChr Char | ShFun String [Shape] | ShAny

shapeOf :: S.Term -> Shape
shapeOf = \case
  S.Atom "nil" -> ShNil
  S.Atom a -> ShAtom a
  S.Compound "cons" [h, t] -> ShCons (shapeOf h) (shapeOf t)
  S.Compound f as -> ShFun f (map shapeOf as)
  S.IntLit k -> ShInt k
  S.CharLit c -> ShChr c
  _ -> ShAny

-- | Whether no term matches both shapes. Different constants and different
-- functors (by name or arity) never unify.
shapesDisjoint :: Shape -> Shape -> Bool
shapesDisjoint a b = case (a, b) of
  (ShAny, _) -> False
  (_, ShAny) -> False
  (ShNil, ShNil) -> False
  (ShInt x, ShInt y) -> x /= y
  (ShAtom x, ShAtom y) -> x /= y
  (ShChr x, ShChr y) -> x /= y
  (ShCons h1 t1, ShCons h2 t2) -> shapesDisjoint h1 h2 || shapesDisjoint t1 t2
  (ShFun f as, ShFun g bs) -> f /= g || length as /= length bs || or (zipWith shapesDisjoint as bs)
  _ -> True

-- | Whether the two heads' input patterns differ at some path.
headsExclusive :: Int -> S.Clause -> S.Clause -> Bool
headsExclusive inCount ci cj = or [shapesDisjoint (shapeOf a) (shapeOf b) | (a, b) <- zip (inputs ci) (inputs cj)]
  where
    inputs cl = case S.clauseHead cl of
      S.Compound _ as -> take inCount as
      _ -> []

-- | Integer bounds on a path (inclusive) and values excluded by @!=@.
data IntRange = IntRange (Maybe Integer) (Maybe Integer) [Integer]

-- | Whether no input can satisfy the heads and guards of both clauses. The
-- compiled code only gets this far with integers at guarded paths (other
-- values go to the interpreter), so integer ranges are enough.
clausesExclusive :: Int -> S.Clause -> S.Clause -> Bool
clausesExclusive inCount ci cj =
  or [shapesDisjoint (shapeOf a) (shapeOf b) | (a, b) <- zip (inputs ci) (inputs cj)]
    || or [rangesDisjoint r1 r2 | (path, r1) <- M.toList rangesI, Just r2 <- [M.lookup path rangesJ]]
    || or [contradicts g1 g2 | g1 <- relsI, g2 <- relsJ]
    || or [rangesDisjoint r1 r2 | (e, r1) <- M.toList exprsI, Just r2 <- [M.lookup e exprsJ]]
  where
    exprsI = exprConstraints (inputs ci) (S.clauseBody ci)
    exprsJ = exprConstraints (inputs cj) (S.clauseBody cj)
    inputs cl = case S.clauseHead cl of
      S.Compound _ as -> take inCount as
      _ -> []
    (rangesI, relsI) = clauseConstraints (inputs ci) (S.clauseBody ci)
    (rangesJ, relsJ) = clauseConstraints (inputs cj) (S.clauseBody cj)
    rangesDisjoint (IntRange lo1 hi1 ex1) (IntRange lo2 hi2 ex2) =
      let lo = maxBound' lo1 lo2
          hi = minBound' hi1 hi2
       in case (lo, hi) of
            (Just l, Just h) -> l > h || (l == h && l `elem` (ex1 ++ ex2))
            _ -> False
    maxBound' a b = case (a, b) of
      (Just x, Just y) -> Just (max x y)
      _ -> maybe b Just a
    minBound' a b = case (a, b) of
      (Just x, Just y) -> Just (min x y)
      _ -> maybe b Just a
    contradicts (x1, op1, y1) (x2, op2, y2)
      | x1 == x2 && y1 == y2 = clash op1 op2
      | x1 == y2 && y1 == x2 = clash op1 (flipCmp op2)
      | otherwise = False
    clash a b = (a, b) `elem` [("gt", "lt"), ("gt", "lte"), ("lt", "gt"), ("lt", "gte"), ("gte", "lt"), ("lte", "gt")]

flipCmp :: String -> String
flipCmp = \case
  "gt" -> "lt"
  "lt" -> "gt"
  "gte" -> "lte"
  "lte" -> "gte"
  op -> op

-- | Integer ranges per head path, from literals in the head and guards
-- against literals, and comparisons between two head paths.
clauseConstraints :: [S.Term] -> [S.Term] -> (M.Map ArgPath IntRange, [(ArgPath, String, ArgPath)])
clauseConstraints headArgs body = (foldl refineRange litRanges guards, relations)
  where
    walk path = \case
      S.Var v | v >= 0 -> [(Left v, path)]
      S.IntLit k -> [(Right k, path)]
      S.Compound "cons" [h, t] -> walk (second' (++ [1]) path) h ++ walk (second' (++ [2]) path) t
      _ -> []
    second' f (a, b) = (a, f b)
    occurrences = concat [walk (i, []) a | (i, a) <- zip [0 ..] headArgs]
    varPaths = M.fromListWith (\_ first -> first) [(v, path) | (Left v, path) <- occurrences]
    litRanges = M.fromList [(path, IntRange (Just k) (Just k) []) | (Right k, path) <- occurrences]
    operand = \case
      S.Var v | Just path <- M.lookup v varPaths -> Just (Left path)
      S.IntLit k -> Just (Right k)
      _ -> Nothing
    cmps = [(op, a, b) | S.Compound op [l, r] <- body, isCmpOp op, Just a <- [operand l], Just b <- [operand r]]
    guards = [(x, op, k) | (op, Left x, Right k) <- cmps] ++ [(x, flipCmp op, k) | (op, Right k, Left x) <- cmps]
    relations = [(x, op, y) | (op, Left x, Left y) <- cmps, op /= "neq"]

-- | Integer ranges on arithmetic expressions over head paths, from guards
-- that evaluate them: @k is E@ (E equals k), @X is E@ followed by a
-- comparison or @!=@ on X, and a comparison of E with a literal. Each
-- expression is keyed by its form with head variables replaced by their
-- paths, so the same key in two clauses of one predicate is the same value
-- for the same call. @!=@ is structural, so it counts only on a variable
-- defined by @is@, which holds an evaluated integer.
exprConstraints :: [S.Term] -> [S.Term] -> M.Map S.Term IntRange
exprConstraints headArgs body = fst (exprFacts headArgs body)

-- | 'exprConstraints', and the divisor of every @%@ the clause's guards
-- evaluate, keyed the same way ('Nothing' where it has no key). Structural
-- @!=@ evaluates nothing.
exprFacts :: [S.Term] -> [S.Term] -> (M.Map S.Term IntRange, [Maybe S.Term])
exprFacts headArgs body = go M.empty (M.empty, []) body
  where
    walk path = \case
      S.Var v | v >= 0 -> [(v, path)]
      S.Compound "cons" [h, t] -> walk (fst path, snd path ++ [1]) h ++ walk (fst path, snd path ++ [2]) t
      _ -> []
    varPaths = M.fromListWith (\_ first -> first) (concat [walk (i, []) a | (i, a) <- zip [0 ..] headArgs])
    pathTerm (i, offs) = S.Compound "$path" (map (S.IntLit . fromIntegral) (i : offs))
    keyOf defs = \case
      S.Var v
        | Just path <- M.lookup v varPaths -> Just (pathTerm path)
        | Just e <- M.lookup v defs -> Just e
      S.IntLit k -> Just (S.IntLit k)
      S.Compound op as | op `elem` ["plus", "minus", "mul", "mod"] -> S.Compound op <$> mapM (keyOf defs) as
      _ -> Nothing
    -- Only an expression that is not a lone head path: those are ranged by
    -- 'clauseConstraints' already.
    exprKey defs t = case keyOf defs t of
      Just e@(S.Compound op _) | op /= "$path" -> Just e
      _ -> Nothing
    defined defs = \case
      S.Var v -> M.member v defs
      _ -> False
    divisorsIn defs = \case
      S.Compound "mod" [a, b] -> keyOf defs b : divisorsIn defs a ++ divisorsIn defs b
      S.Compound _ as -> concatMap (divisorsIn defs) as
      _ -> []
    evaluated defs = \case
      S.Compound "is" [_, e] -> divisorsIn defs e
      S.Compound op [l, r] | isCmpOp op, op /= "neq" -> divisorsIn defs l ++ divisorsIn defs r
      _ -> []
    go defs (ranges, divs) = \case
      [] -> (ranges, divs)
      g : gs ->
        let acc' r = (r, divs ++ evaluated defs g)
         in case g of
              S.Compound "is" [S.Var x, e]
                | x >= 0,
                  not (M.member x varPaths),
                  not (M.member x defs),
                  Just key <- exprKey defs e ->
                    go (M.insert x key defs) (acc' ranges) gs
              S.Compound "is" [S.IntLit k, e]
                | Just key <- exprKey defs e -> go defs (acc' (refineRange ranges (key, "eq", k))) gs
              S.Compound op [l, r]
                | isCmpOp op,
                  op /= "neq" || defined defs l || defined defs r ->
                    case (l, r) of
                      (_, S.IntLit k) | Just key <- exprKey defs l -> go defs (acc' (refineRange ranges (key, op, k))) gs
                      (S.IntLit k, _) | Just key <- exprKey defs r -> go defs (acc' (refineRange ranges (key, flipCmp op, k))) gs
                      _ -> go defs (acc' ranges) gs
              _ -> go defs (acc' ranges) gs

-- | Committing to an earlier clause skips a later one, so the later one must
-- not be able to raise an error the earlier one would not. On the compiled
-- path the only arithmetic error is a zero divisor: every @%@ the later
-- clause evaluates must divide by a non-zero literal or by a divisor the
-- earlier clause evaluates (which raises first, and is a bailout there).
laterRaisesNothingNew :: Int -> S.Clause -> S.Clause -> Bool
laterRaisesNothingNew inCount ci cj = all safe (snd (facts cj))
  where
    facts cl = exprFacts (inputs cl) (S.clauseBody cl)
    inputs cl = case S.clauseHead cl of
      S.Compound _ as -> take inCount as
      _ -> []
    earlier = snd (facts ci)
    safe = \case
      Just (S.IntLit k) -> k /= 0
      Just d -> Just d `elem` earlier
      Nothing -> False

-- | Narrow the range at a key by @key op k@; @neq@ excludes a value and
-- @eq@ pins it.
refineRange :: Ord k => M.Map k IntRange -> (k, String, Integer) -> M.Map k IntRange
refineRange ranges (x, op, k) =
  let IntRange lo hi ex = M.findWithDefault (IntRange Nothing Nothing []) x ranges
      tighten = case op of
        "gt" -> IntRange (Just (maybe (k + 1) (max (k + 1)) lo)) hi ex
        "gte" -> IntRange (Just (maybe k (max k) lo)) hi ex
        "lt" -> IntRange lo (Just (maybe (k - 1) (min (k - 1)) hi)) ex
        "lte" -> IntRange lo (Just (maybe k (min k) hi)) ex
        "eq" -> IntRange (Just (maybe k (max k) lo)) (Just (maybe k (min k) hi)) ex
        _ -> IntRange lo hi (k : ex)
   in M.insert x tighten ranges


-- | Guards the compiler accepts, by the parser's names: the arithmetic
-- comparisons (both sides evaluated) and structural @!=@. Unification and
-- @==@ are not integer tests and stay with the interpreter.
isCmpOp :: String -> Bool
isCmpOp op = op `elem` ["gt", "lt", "gte", "lte", "neq"]
