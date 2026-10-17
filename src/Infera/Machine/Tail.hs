-- | A conservative source and argument gate for native tail calls.
-- A closed first-order call graph may include pure helpers and mutual
-- recursion. Runtime control still proves the call is in tail position and
-- that retiring its parent cannot discard a delayed contract or cut owner.
-- Frozen branches own their rollback state independently of the active heap.
module Infera.Machine.Tail
  ( eligiblePredicate,
    eligibleFuelReuse,
    eligibleArguments,
  )
where

import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import Infera.Infer (builtinDet)
import Infera.Program (Pred (..), Program, Signature, lookupPred, predIsDynamic, predIsTabled, predIsUnsafe)
import Infera.Syntax (Clause (..), Term (..), functorOf)
import Infera.Unify (isGroundTerm)

-- | A ground argument cannot change while the child runs, so its declared
-- output/sort checks remain valid. An undeclared call has no delayed output
-- contract and may carry free/structured data. Internal cut markers are
-- excluded even in data: a retired activation must not be targeted later.
eligibleArguments :: Maybe Signature -> [Term] -> Bool
eligibleArguments signature arguments = all withoutCut arguments
  && (signature == Nothing || all isGroundTerm arguments)

-- | Prove that every reachable definition stays within native first-order
-- arithmetic, equality, guards, closed control trees and direct user calls.
-- A revisit closes a pure strongly connected component: its first visit still
-- checks all clauses, so an effect in any other branch cannot hide behind a
-- recursive edge.
--
-- Helpers and opaque pure controls may finish before the tail call, and mutual
-- recursion may transfer between different predicates. Each control child is
-- proved as source, including both alternatives and every conditional arm.
-- Meta-call arguments are never treated as trusted source. The runtime task
-- stack, rather than clause syntax, establishes which completed activation can
-- actually be retired.
-- Internal cut markers are forbidden even in nested data.
eligiblePredicate :: Program -> Pred -> Bool
eligiblePredicate = provePredicate True

-- | Preserve the historical default-query depth budget policy separately
-- from physical frame retirement. Closed controls can retire completed
-- activations without refunding their logical resolution fuel. In particular,
-- widening the purity proof must not turn a previously exhausted scoped loop
-- into a successful query merely by discarding its completed return frames.
eligibleFuelReuse :: Program -> Pred -> Bool
eligibleFuelReuse = provePredicate False

provePredicate :: Bool -> Program -> Pred -> Bool
provePredicate controls program definition = case prove Set.empty definition of
  Just _ -> True
  Nothing -> False
  where
    -- Thread one set through every sibling goal and clause. Rechecking a
    -- shared descendant independently on each path makes a diamond-shaped
    -- acyclic call graph exponentially expensive to prove.
    prove visited target
      | predKey target `Set.member` visited = Just visited
      | predIsUnsafe program target || predIsDynamic program target
          || predIsTabled program target || null clauses = Nothing
      | otherwise = foldM (eligibleClause target) (Set.insert (predKey target) visited) clauses
      where
        clauses = IM.elems (predClauses target)
    eligibleClause target visited clause
      | functorOf (clauseHead clause) /= Just (predKey target)
          || not (all withoutCut (clauseHead clause : clauseBody clause)) = Nothing
      | otherwise = foldM eligibleGoal visited (clauseBody clause)
    eligibleGoal visited (Compound name children)
      | controls && ((name `elem` [",", ";", "->"] && length children == 2)
          || (name `elem` ["once", "not"] && length children == 1)) =
          foldM eligibleGoal visited children
    eligibleGoal visited goal
      | nativeGoal goal = Just visited
      | otherwise = case functorOf goal of
          Just key@(name, arity)
            -- Builtin dispatch precedes user predicate lookup. Reject
            -- every non-native builtin even if its name is redefined.
            | builtinDet name arity == Nothing,
              Just target <- lookupPred key program -> prove visited target
          _ -> Nothing

nativeGoal :: Term -> Bool
nativeGoal (Atom name) = name `elem` ["true", "fail", "false"]
nativeGoal (Compound name [_, _]) =
  name `elem` ["unify", "equiv", "is", "gt", "lt", "gte", "lte"]
nativeGoal _ = False

withoutCut :: Term -> Bool
withoutCut (Compound "$cut" _) = False
withoutCut (Compound _ arguments) = all withoutCut arguments
withoutCut _ = True
