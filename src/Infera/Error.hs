-- | Runtime errors raised by the Infera engine.
module Infera.Error
  ( SolveError (..),
    PredKey,
    showPredKey,
    showSolveError,
  )
where

import Infera.Syntax

-- | A predicate is identified by name and arity.
type PredKey = (String, Int)

showPredKey :: PredKey -> String
showPredKey (n, a) = n ++ "/" ++ show a

data SolveError
  = InstantiationError Term
  | ExpectedInteger Term
  | ExpectedNumber Term
  | DivisionByZero
  | NegativeIntegerExponent Integer
  | UnknownPredicate PredKey
  | -- | Declared input argument (1-based) was not ground at call time.
    ModeError PredKey Int Term
  | -- | Declared output argument (1-based) was not ground after the call.
    OutputModeError PredKey Int Term
  | -- | Argument (1-based) does not have the declared sort.
    SortError PredKey Int Sort Term
  | -- | Declared determinism was violated: expected category, solutions found.
    DetError PredKey Det Int
  | -- | A CLP(Z) variable was bound to a non-integer.
    CLPTypeError Term
  | -- | Labeling requested on a variable with an unbounded domain.
    UnboundedDomain Term
  | TypeError String Term
  | UserError String
  deriving (Show, Eq)

showSolveError :: SolveError -> String
showSolveError err = case err of
  InstantiationError t ->
    "arithmetic expression is not sufficiently instantiated: " ++ show t
  ExpectedInteger t -> "expected an integer expression, but got: " ++ show t
  ExpectedNumber t -> "expected a numeric expression, but got: " ++ show t
  DivisionByZero -> "division by zero"
  NegativeIntegerExponent n ->
    "negative exponent in integer exponentiation: " ++ show n
  UnknownPredicate k -> "unknown predicate: " ++ showPredKey k
  ModeError k i t ->
    "mode error: argument "
      ++ show i
      ++ " of "
      ++ showPredKey k
      ++ " is declared input (<=) but is not ground: "
      ++ show t
  OutputModeError k i t ->
    "mode error: argument "
      ++ show i
      ++ " of "
      ++ showPredKey k
      ++ " is declared output (=>) but is not ground after the call: "
      ++ show t
  SortError k i s t ->
    "sort error: argument "
      ++ show i
      ++ " of "
      ++ showPredKey k
      ++ " must be "
      ++ showSort s
      ++ ", but got: "
      ++ show t
  DetError k d n ->
    "determinism error: "
      ++ showPredKey k
      ++ " is declared "
      ++ showDet d
      ++ " but "
      ++ describe n
    where
      describe 0 = "failed"
      describe m = "produced " ++ show m ++ " solutions"
  CLPTypeError t -> "CLP(Z) variable bound to a non-integer: " ++ show t
  UnboundedDomain t -> "cannot label a variable with an unbounded domain: " ++ show t
  TypeError what t -> "type error: expected " ++ what ++ ", but got: " ++ show t
  UserError msg -> msg
