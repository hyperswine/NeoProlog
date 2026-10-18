-- | Constraint operations shared with the propagator, without constructing a
-- reference search or a SolverState per labeling node. The core owns choices,
-- bindings and rollback; the persistent propagation kernel remains unchanged.
module Infera.Core.Constraint
  ( post, labelVariables, minimumVariables, LabelStep (..), selectLabel,
    minimumCost, boundMinimum,
  ) where

import Data.List (nub, sortOn)
import Infera.Arith (evalIntExpr)
import Infera.CLP
import Infera.Error (SolveError (..))
import Infera.Syntax (Term (..), VarId, unfoldCons)
import Infera.Unify (deepWalk, walk, termVars)

type Checked = Either SolveError (Maybe Store)

-- Only exact builtin arities enter this path. Malformed calls retain normal
-- dispatch, including a user definition at another arity.
post :: Store -> String -> [Term] -> Maybe Checked
post store name arguments = case (name, arguments) of
  ("neq", [a, b]) -> Just (addDiseq a b store)
  ("int_eq", [a, b]) -> relation RelEq a b
  ("fd_ne", [a, b]) -> relation RelNe a b
  ("fd_le", [a, b]) -> relation RelLe a b
  ("fd_lt", [a, b]) -> relation RelLe (plusOne a) b
  ("fd_ge", [a, b]) -> relation RelLe b a
  ("fd_gt", [a, b]) -> relation RelLe (plusOne b) a
  ("in", [target, range]) -> Just $ case deepWalk substitution range of
    Compound "range" [lo, hi]
      | Just lower <- parseBound lo, Just upper <- parseBound hi ->
          let targets = case deepWalk substitution target of
                list@(Compound "cons" _) -> fst (unfoldCons list)
                term -> [term]
           in addDomains targets lower upper store
    other -> Left (TypeError "range (Lo..Hi)" other)
  ("all_different", [list]) -> Just (different list)
  ("all_distinct", [list]) -> Just (different list)
  ("reify", [raw, truth]) -> Just $ case walk substitution raw of
    Compound "int_eq" [a, b] -> addReified RelEq a b truth store
    Compound "fd_ne" [a, b] -> addReified RelNe a b truth store
    Compound "fd_le" [a, b] -> addReified RelLe a b truth store
    Compound "fd_lt" [a, b] -> addReified RelLe (plusOne a) b truth store
    Compound "fd_ge" [a, b] -> addReified RelLe b a truth store
    Compound "fd_gt" [a, b] -> addReified RelLe (plusOne b) a truth store
    other@(Var _) -> Left (InstantiationError other)
    other -> Left (TypeError "integer relation (#=, #!=, #<, #<=, #>, #>=)" other)
  _ -> Nothing
  where
    substitution = stSubst store
    relation rel a b = Just (addRelation rel a b store)
    different raw = case unfoldCons (deepWalk substitution raw) of
      (xs, Nothing) -> addAllDifferent xs store
      _ -> Left (InstantiationError (deepWalk substitution raw))
    plusOne a = Compound "plus" [a, IntLit 1]
    parseBound (IntLit n) = Just (Fin n)
    parseBound (Atom "inf") = Just NegInf
    parseBound (Atom "sup") = Just PosInf
    parseBound _ = Nothing

-- Ordinary label deliberately retains the reference's permissive list-tail
-- policy. Optimization has a separate, strict proper-integer-list contract.
labelVariables :: Store -> Term -> [VarId]
labelVariables store raw = nub (concatMap termVars (fst (unfoldCons (deepWalk (stSubst store) raw))))

minimumVariables :: Store -> Term -> Either SolveError [VarId]
minimumVariables store raw = case unfoldCons list of
  (_, Just _) -> Left (TypeError "proper list of integer variables" list)
  (xs, Nothing)
    | any invalid xs -> Left (TypeError "list of integer variables" list)
    | otherwise -> Right (nub (concatMap termVars xs))
  where
    list = deepWalk (stSubst store) raw
    invalid (Var _) = False
    invalid (IntLit _) = False
    invalid _ = True

data LabelStep = LabelDone | LabelNext [VarId] VarId [Integer]
  deriving (Eq, Show)

-- Keep stable smallest-domain-first selection and ascending enumeration.
-- Minimum follows aliases anew at each node; ordinary label keeps its
-- historical representative test. The distinction is observable on aliases.
selectLabel :: Bool -> Store -> [VarId] -> Either SolveError LabelStep
selectLabel minimizing store variables = case pending of
  [] -> Right LabelDone
  _ -> case [v | (v, Nothing) <- sizes] of
    v : _ -> Left (UnboundedDomain (Var v))
    [] -> case sortOn snd sizes of
      (v, _) : _ -> Right (LabelNext pending v (maybe [] id (domainOf store v >>= domainValues)))
      [] -> Right LabelDone
  where
    substitution = stSubst store
    pending
      | minimizing = nub [w | v <- variables, Var w <- [walk substitution (Var v)]]
      | otherwise = [v | v <- variables, Var w <- [walk substitution (Var v)], w == v]
    sizes = [(v, domainOf store v >>= domainSize) | v <- pending]

boundMinimum :: Term -> Maybe Integer -> Store -> Checked
boundMinimum _ Nothing store = Right (Just store)
boundMinimum cost (Just value) store = addRelation RelLe cost (IntLit (value - 1)) store

minimumCost :: Store -> Term -> Either SolveError Integer
minimumCost store cost = case evalIntExpr (stSubst store) cost of
  Left err -> Left err
  Right Nothing -> Left (InstantiationError (deepWalk (stSubst store) cost))
  Right (Just value) -> Right value
