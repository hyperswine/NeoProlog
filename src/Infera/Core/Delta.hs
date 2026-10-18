-- | The deliberately narrow proof used by the core's incremental tables.
--
-- Only a positive, same-variant self-call at the beginning of a clause may
-- consume the previous round's new answers. Its suffix, and every base
-- clause, must be acyclic, effect-free goals without declared contracts.
-- Keep this separate from compiled plans: their indexing and matching may
-- become more selective without broadening the semantic proof.
module Infera.Core.Delta (recursiveClauses) where

import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import Infera.Arith (normArithTerm)
import qualified Infera.Engine.Contracts as Contracts
import Infera.Infer (builtinDet)
import qualified Infera.Program as P
import Infera.Syntax (Term (..), clauseBody, clauseHead, functorOf, termVarIds)
import Infera.Unify (canonicalize, emptySubst, renameTerm, unifyPlain)

-- | Compiled clause ordinals that may run after the first round, or Nothing
-- when the general fixpoint evaluator must be retained. The call is already
-- dereferenced, canonical and known not to mention a constrained variable.
-- As in the reference evaluator, errors, exhaustion and foreign incomplete
-- dependencies encountered at runtime invalidate this proof's fast path.
recursiveClauses :: P.Program -> P.Pred -> Term -> Maybe [Int]
recursiveClauses program predicate call
  | not (safeContract predicate) || Contracts.commitsAfterSuccess predicate Nothing args = Nothing
  | otherwise = map fst . filter snd <$> mapM classify candidates
  where
    key = P.predKey predicate
    args = case call of Compound _ as -> as; _ -> []
    selected = Set.fromList (P.candidateClauses predicate
      (if P.predIsIndexed program predicate then map P.indexKey args else []))
    -- Compilation preserves ascending source-clause order, even if callers
    -- supplied a predicate whose IntMap clause keys are not consecutive.
    candidates = [(ordinal, clause) | (ordinal, (sourceId, clause)) <- zip [0 ..] (IM.toAscList (P.predClauses predicate)),
                                     Set.member sourceId selected]
    classify (ordinal, clause) = case clauseBody clause of
      recursive : rest | functorOf recursive == Just key ->
        if all (safeGoal (Set.singleton key)) rest && sameVariant clause recursive
          then Just (ordinal, True)
          else Nothing
      body | all (safeGoal (Set.singleton key)) body -> Just (ordinal, False)
      _ -> Nothing
    sameVariant clause recursive =
      -- The exported call already contains all entry bindings. Alpha-rename
      -- the source variables above its canonical variables before matching;
      -- unrelated constraint-store identities cannot affect this proof.
      let base = 1 + maximum (-1 : termVarIds call)
       in case unifyPlain emptySubst call (renameTerm base (clauseHead clause)) of
            Nothing -> True -- This clause cannot contribute to this variant.
            Just subst -> fst (canonicalize subst (normArithTerm subst (renameTerm base recursive))) == call
    safeContract p = null (P.predDecls p)
      && not (P.predIsUnsafe program p) && not (P.predIsDynamic program p)
    safeGoal _ (Atom name) | name `elem` ["true", "fail", "false"] = True
    safeGoal _ (Compound "unify" [_, _]) = True
    safeGoal seen term = case functorOf term of
      Just target@(name, arity) | builtinDet name arity == Nothing && Set.notMember target seen ->
        case P.lookupPred target program of
          Just p -> safeContract p && all (all (safeGoal (Set.insert target seen)) . clauseBody) (IM.elems (P.predClauses p))
          Nothing -> False
      _ -> False
