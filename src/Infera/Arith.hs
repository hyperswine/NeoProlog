-- | Safe numeric evaluation of arithmetic terms.
module Infera.Arith
  ( NumericValue (..),
    numericTerm,
    numericDouble,
    evalNumeric,
    evalArithSafe,
    evalIntExpr,
    arithOps,
    normArithTerm,
    deepEval,
    compareNumeric,
  )
where

import Infera.Error
import Infera.Syntax
import Infera.Unify

data NumericValue
  = NVInt Integer
  | NVFloat Double
  deriving (Show, Eq)

numericTerm :: NumericValue -> Term
numericTerm (NVInt n) = IntLit n
numericTerm (NVFloat d) = FloatLit d

numericDouble :: NumericValue -> Double
numericDouble (NVInt n) = fromIntegral n
numericDouble (NVFloat d) = d

compareNumeric :: NumericValue -> NumericValue -> Ordering
compareNumeric (NVInt a) (NVInt b) = compare a b
compareNumeric a b = compare (numericDouble a) (numericDouble b)

arithOps :: [String]
arithOps = ["plus", "minus", "mul", "div", "mod", "^", "neg", "abs", "min", "max"]

-- | Evaluate an arithmetic expression.  @Right Nothing@ means the expression is
-- blocked on an unbound variable; malformed expressions are explicit errors.
evalNumeric :: Subst -> Term -> Either SolveError (Maybe NumericValue)
evalNumeric s term = case walk s term of
  Var _ -> Right Nothing
  IntLit n -> Right (Just (NVInt n))
  FloatLit d -> Right (Just (NVFloat d))
  Compound "plus" [a, b] -> numericBinOp (+) (+) s a b
  Compound "minus" [a, b] -> numericBinOp (-) (-) s a b
  Compound "mul" [a, b] -> numericBinOp (*) (*) s a b
  Compound "min" [a, b] -> numericBinOp min min s a b
  Compound "max" [a, b] -> numericBinOp max max s a b
  Compound "neg" [a] -> fmap (fmap neg) (evalNumeric s a)
  Compound "abs" [a] -> fmap (fmap absN) (evalNumeric s a)
  Compound "div" [a, b] -> do
    ma <- evalNumeric s a
    mb <- evalNumeric s b
    case (ma, mb) of
      (_, Just (NVInt 0)) -> Left DivisionByZero
      (_, Just (NVFloat 0)) -> Left DivisionByZero
      (Just (NVInt x), Just (NVInt y)) -> Right (Just (NVInt (x `div` y)))
      (Just x, Just y) -> Right (Just (NVFloat (numericDouble x / numericDouble y)))
      _ -> Right Nothing
  Compound "mod" [a, b] -> do
    ma <- evalNumeric s a
    mb <- evalNumeric s b
    case (ma, mb) of
      (_, Just (NVInt 0)) -> Left DivisionByZero
      (Just (NVInt x), Just (NVInt y)) -> Right (Just (NVInt (x `mod` y)))
      (Just _, Just bad) -> Left (ExpectedInteger (numericTerm bad))
      _ -> Right Nothing
  Compound "^" [a, b] -> do
    ma <- evalNumeric s a
    mb <- evalNumeric s b
    case (ma, mb) of
      (_, Just (NVInt e)) | e < 0 -> Left (NegativeIntegerExponent e)
      (Just (NVInt base), Just (NVInt e)) -> Right (Just (NVInt (base ^ e)))
      (Just base, Just e) -> Right (Just (NVFloat (numericDouble base ** numericDouble e)))
      _ -> Right Nothing
  bad -> Left (ExpectedNumber (deepWalk s bad))
  where
    neg (NVInt n) = NVInt (negate n)
    neg (NVFloat d) = NVFloat (negate d)
    absN (NVInt n) = NVInt (abs n)
    absN (NVFloat d) = NVFloat (abs d)

numericBinOp ::
  (Integer -> Integer -> Integer) ->
  (Double -> Double -> Double) ->
  Subst ->
  Term ->
  Term ->
  Either SolveError (Maybe NumericValue)
numericBinOp iop fop s a b = do
  ma <- evalNumeric s a
  mb <- evalNumeric s b
  pure $ case (ma, mb) of
    (Just (NVInt x), Just (NVInt y)) -> Just (NVInt (iop x y))
    (Just x, Just y) -> Just (NVFloat (fop (numericDouble x) (numericDouble y)))
    _ -> Nothing

evalArithSafe :: Subst -> Term -> Either SolveError (Maybe Term)
evalArithSafe s t = fmap (fmap numericTerm) (evalNumeric s t)

-- | Integer-only evaluation (used by CLP(Z) for ground checks).
evalIntExpr :: Subst -> Term -> Either SolveError (Maybe Integer)
evalIntExpr s t = do
  r <- evalNumeric s t
  case r of
    Nothing -> Right Nothing
    Just (NVInt n) -> Right (Just n)
    Just bad -> Left (ExpectedInteger (numericTerm bad))

-- | Eagerly reduce fully-ground arithmetic subexpressions (used before head
-- unification so that @fact (N - 1) R@ calls @fact 4 R@).  Errors are left in
-- symbolic form.
normArithTerm :: Subst -> Term -> Term
normArithTerm s t = case walk s t of
  Compound f as
    | f `elem` arithOps ->
        let as' = map (normArithTerm s) as
            t' = Compound f as'
         in case evalArithSafe emptySubst t' of
              Right (Just v) -> v
              _ -> t'
    | otherwise -> Compound f (map (normArithTerm s) as)
  t' -> t'

-- | Dereference and evaluate ground arithmetic (used when rendering answers).
deepEval :: Subst -> Term -> Term
deepEval s t = tryEval (deepWalk s t)
  where
    tryEval t' = case t' of
      Compound f as
        | f `elem` arithOps ->
            let t'' = Compound f (map tryEval as)
             in case evalArithSafe emptySubst t'' of
                  Right (Just v) -> v
                  _ -> t''
        | otherwise -> Compound f (map tryEval as)
      _ -> t'
