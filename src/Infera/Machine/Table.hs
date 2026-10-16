-- | Native variant-table fixedpoints. Table keys and answers contain canonical
-- syntax only, so no heap address can escape into a persistent table entry.
-- Clause bodies run through the supplied native driver, never the reference
-- interpreter. Persistent head unification and CLP checks use the same store
-- algorithms as the heap-backed adapter.
module Infera.Machine.Table (evalTabled, evalTabledTraced, evalTabledTracedWithContext, InstrumentedSearch) where

import qualified Data.IntMap.Strict as IM
import Data.List (foldl', nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Infera.Arith (normArithTerm)
import Infera.CLP (Store (..), isConstrained, storeUnify)
import Infera.Engine.Reference (Env (..), OutputEvent (..), Search, SearchItem (..), SolverState (..), TableEntry (..))
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Engine.Contracts as Contracts
import Infera.Infer (builtinDet)
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program
import Infera.Syntax
import Infera.Unify (canonicalize, deepWalk, instantiate, renameBody, renameTerm)

-- Stop alternatives at a source cut, retaining the marker for the owning
-- activation. The marker is consumed only after all clause alternatives have
-- been combined, so cuts cannot accidentally expose later clauses.
thenSearch :: Search -> Search -> Search
thenSearch [] rest = rest
thenSearch (marker@(CutMarker _) : _) _ = [marker]
thenSearch (item : items) rest = item : thenSearch items rest

alts :: [Search] -> Search
alts = foldr thenSearch []

isExhausted :: SearchItem -> Bool
isExhausted BranchExhausted = True
isExhausted _ = False

consumeMarkers :: Int -> Search -> Search
consumeMarkers owner = filter keep
  where
    keep (CutMarker found) = found /= owner
    keep _ = True

emit :: OutputEvent -> SolverState -> SolverState
emit event state = state {ssOutput = event : ssOutput state, ssOutLen = ssOutLen state + 1}

-- The table activation itself owns contract checking in Control. These raw
-- clause evaluations deliberately do not select a signature or commit again.
evalClauses :: (Env -> Int -> SolverState -> [Term] -> Search) -> Env -> Int -> SolverState -> Pred -> Term -> [Term] -> Search
evalClauses solveNative environment fuel state predicate goal arguments
  | fuel <= 0 = [BranchExhausted]
  | otherwise =
      let keys = if predIsIndexed (envProg environment) predicate then map indexKey arguments else []
          candidates = candidateClauses predicate keys
          owner = ssFresh state
       in consumeMarkers owner (alts
            [tryClause solveNative environment fuel state owner goal (predClauses predicate IM.! index)
             | index <- candidates])

tryClause :: (Env -> Int -> SolverState -> [Term] -> Search) -> Env -> Int -> SolverState -> Int -> Term -> Clause -> Search
tryClause solveNative environment fuel state owner goal clause =
  let headTerm = renameTerm owner (clauseHead clause)
      body = map (renameBody owner) (clauseBody clause)
      fresh = owner + max 1 (clauseNVars clause)
      prepared = state {ssFresh = fresh}
   in case storeUnify (ssStore prepared) goal headTerm of
        Left err -> [BranchError err]
        Right Nothing -> []
        Right (Just store) -> solveNative environment (fuel - 1) prepared {ssStore = store} body

-- | Tabled evaluation (linear tabling with fixpoint iteration). Positive
-- same-variant linear recursion consumes only the preceding round's new
-- answers. Other recursive shapes retain the general fixpoint evaluator.
-- Calls whose arguments involve constrained variables, and answers that carry
-- constraints, fall back to plain evaluation.
evalTabled :: (Env -> Int -> SolverState -> [Term] -> Search) -> Env -> Int -> SolverState -> Pred -> Term -> Search
evalTabled solveNative env fuel st0 p goal
  | any (isConstrained store0) callVars = plain st0
  | otherwise = case Map.lookup callKey (ssTables st0) of
      Just te
        | teComplete te -> [BranchExhausted | teTruncated te] ++ consumeAnswers st0 (teAnswers te)
        | otherwise -> ConsumedIncomplete callKey : consumeAnswers st0 (teAnswers te)
      Nothing -> fixpoint (case deltaClauses of Just _ -> True; Nothing -> False)
        (0 :: Int) (ssTables st0) [] Set.empty []
  where
    store0 = ssStore st0
    s0 = stSubst store0
    (callKey, callVars) = canonicalize s0 goal
    argsW = case deepWalk s0 goal of Compound _ as -> as; _ -> []
    plain st = evalClauses solveNative env fuel st p goal argsW

    -- A delta is sound only when removing an old derivation cannot change a
    -- later call's behaviour. Keep the initial fast path deliberately narrow:
    -- one self-call first in a clause, exactly the current variant, followed
    -- by acyclic positive goals with no declared contracts, effects or CLP.
    -- In particular this excludes mutual/nonlinear recursion and all control
    -- constructs; their ordering, errors and cuts still use the old evaluator.
    deltaClauses
      | not (safeContract p) || inferredCommit = Nothing
      | otherwise = fmap (map fst . filter snd) (mapM classifyClause candidates)
      where
        inferredCommit = Contracts.commitsAfterSuccess p Nothing argsW
        candidates = candidateClauses p
          (if predIsIndexed (envProg env) p then map indexKey argsW else [])
        classifyClause ci =
          let cl = predClauses p IM.! ci
           in case clauseBody cl of
                recursive : rest
                  | functorOf recursive == Just (predKey p) ->
                      if all (safeGoal (Set.singleton (predKey p))) rest && sameVariant cl recursive
                        then Just (ci, True)
                        else Nothing
                body
                  | all (safeGoal (Set.singleton (predKey p))) body -> Just (ci, False)
                  | otherwise -> Nothing
        sameVariant cl recursive =
          let base = ssFresh st0
           in case storeUnify store0 goal (renameTerm base (clauseHead cl)) of
                Left _ -> False
                Right Nothing -> True -- This clause cannot contribute.
                Right (Just store) ->
                  let s = stSubst store
                   in fst (canonicalize s (normArithTerm s (renameTerm base recursive))) == callKey
        safeContract predicate =
          null (predDecls predicate)
            && not (predIsUnsafe (envProg env) predicate)
            && not (predIsDynamic (envProg env) predicate)
        safeGoal _ (Atom name) | name `elem` ["true", "fail", "false"] = True
        safeGoal _ (Compound "unify" [_, _]) = True
        safeGoal seen term = case functorOf term of
          Just key@(name, arity)
            | builtinDet name arity == Nothing && Set.notMember key seen ->
                case lookupPred key (envProg env) of
                  Just predicate ->
                    safeContract predicate
                      && all (all (safeGoal (Set.insert key seen)) . clauseBody)
                        (IM.elems (predClauses predicate))
                  Nothing -> False
          _ -> False

    fixpoint useDelta iteration tables answers answerSet delta =
      let visible = if useDelta then delta else answers
          st1 = st0 {ssTables = Map.insert callKey (TableEntry False False visible answerSet) tables}
          items = case (useDelta && iteration > 0, deltaClauses) of
            (True, Just recursive) ->
              let base = ssFresh st1
               in if fuel <= 0 then [BranchExhausted] else
                    consumeMarkers base (alts
                      [tryClause solveNative env fuel st1 base goal (predClauses p IM.! ci) | ci <- recursive])
            _ -> evalClauses solveNative env fuel st1 p goal argsW
          founds = [stf | Found stf <- items]
          extracted = map extract founds
          unsafe = any (\(_, _, _, bad) -> bad) extracted
          fresh = dedup answerSet [(a, n, o) | (a, n, o, _) <- extracted]
          answers' = answers ++ fresh
          answerSet' = foldl' (\acc (a, _, _) -> Set.insert a acc) answerSet fresh
          deps = nub [k | ConsumedIncomplete k <- items, k /= callKey]
          others = [i | i@(BranchError _) <- items] ++ [BranchExhausted | any isExhausted items]
          completed = Map.unions (Map.filter teComplete tables : [Map.filter teComplete (ssTables stf) | stf <- founds])
          tables' = Map.union completed (Map.delete callKey tables)
          converged = null fresh
          gaveUp = iteration >= Reference.maxTableIterations
          -- Resource exhaustion can make an otherwise independent base clause
          -- observable on every round. Restart with the general algorithm
          -- rather than silently dropping such an issue on subsequent rounds.
          deltaIssue = useDelta && (not (null deps) || not (null others))
       in if deltaIssue
            then fixpoint False 0 (ssTables st0) [] Set.empty []
            else if unsafe
            then plain st0
            else
              if converged || gaveUp
                then
                  let tables'' =
                        if null deps
                          then Map.insert callKey (TableEntry True (not converged) answers' answerSet') tables'
                          else tables'
                      stC = st0 {ssTables = tables''}
                   in map ConsumedIncomplete deps
                        ++ others
                        ++ [BranchExhausted | gaveUp]
                        ++ consumeAnswers stC answers'
                else fixpoint useDelta (iteration + 1) tables' answers' answerSet' fresh

    extract stf =
      let sf = stSubst (ssStore stf)
          (ans, vs) = canonicalize sf goal
          bad = any (isConstrained (ssStore stf)) vs
          out = reverse (take (ssOutLen stf - ssOutLen st0) (ssOutput stf))
       in (ans, length vs, out, bad)

    dedup _ [] = []
    dedup seen ((a, n, o) : rest)
      | Set.member a seen = dedup seen rest
      | otherwise = (a, n, o) : dedup (Set.insert a seen) rest

    consumeAnswers st answers =
      alts
        [ let ans' = instantiate (ssFresh st) ans
              st' = foldl' (flip emit) st {ssFresh = ssFresh st + n} out
           in case storeUnify (ssStore st') goal ans' of
                Left err -> [BranchError err]
                Right Nothing -> []
                Right (Just store) -> [Found st' {ssStore = store}]
        | (ans, n, out) <- answers
        ]


-- A separate opt-in path avoids allocating trace wrappers while ordinary
-- execution consumes canonical table answers and fixedpoint rounds.
type InstrumentedSearch = [Either Trace.TraceEvent SearchItem]

type TracedNative = Env -> Int -> SolverState -> [(Term, Maybe SourceSpan)] -> [Trace.TraceFrame] -> InstrumentedSearch

thenSearchTraced :: InstrumentedSearch -> InstrumentedSearch -> InstrumentedSearch
thenSearchTraced [] rest = rest
thenSearchTraced (marker@(Right (CutMarker _)) : _) _ = [marker]
thenSearchTraced (item : items) rest = item : thenSearchTraced items rest

altsTraced :: [InstrumentedSearch] -> InstrumentedSearch
altsTraced = foldr thenSearchTraced []

consumeMarkersTraced :: Int -> InstrumentedSearch -> InstrumentedSearch
consumeMarkersTraced owner = filter keep
  where
    keep (Right (CutMarker found)) = found /= owner
    keep _ = True

evalClausesTraced :: [Trace.TraceFrame] -> TracedNative -> Env -> Int -> SolverState -> Pred -> Term -> [Term] -> InstrumentedSearch
evalClausesTraced callers solveNative environment fuel state predicate goal arguments
  | fuel <= 0 = [Right BranchExhausted]
  | otherwise =
      let keys = if predIsIndexed (envProg environment) predicate then map indexKey arguments else []
          candidates = candidateClauses predicate keys
          owner = ssFresh state
       in consumeMarkersTraced owner (altsTraced
            [tryClauseTraced callers solveNative environment fuel state owner predicate goal ordinal
             | ordinal <- candidates])

tryClauseTraced :: [Trace.TraceFrame] -> TracedNative -> Env -> Int -> SolverState -> Int -> Pred -> Term -> Int -> InstrumentedSearch
tryClauseTraced callers solveNative environment fuel state owner predicate goal ordinal =
  let clause = predClauses predicate IM.! ordinal
      headTerm = renameTerm owner (clauseHead clause)
      source = Trace.lookupClauseSource (progSources (envProg environment)) (predKey predicate) ordinal
      body = [(renameBody owner template, (\site -> Trace.goalSourceSpan site template) <$> source)
             | template <- clauseBody clause]
      frame = Trace.TraceFrame (predKey predicate) (Just ordinal) (Trace.sourceClauseSpan <$> source)
      fresh = owner + max 1 (clauseNVars clause)
      prepared = state {ssFresh = fresh}
   in case storeUnify (ssStore prepared) goal headTerm of
        Left err ->
          [ Left (Trace.TraceEvent Trace.Exception goal
              (Trace.sourceHeadSpan <$> source) (frame : callers) (Just err)),
            Right (BranchError err)
          ]
        Right Nothing -> []
        Right (Just store) -> solveNative environment (fuel - 1) prepared {ssStore = store} body [frame]

-- | Instrumented fixedpoints keep producer events independent of logical
-- observations. Every actual round is traced, including a delta restart or
-- constrained-answer fallback. Events cannot add answers, dependencies or
-- errors, influence deduplication, or complete an unfinished table.
evalTabledTraced :: TracedNative -> Env -> Int -> SolverState -> Pred -> Term -> InstrumentedSearch
evalTabledTraced = evalTabledTracedWithContext []

-- | Context for events raised before a native body callback starts, such as
-- constrained head-unification errors. Body callbacks already own their
-- enclosing frames; their events pass through without alteration.
evalTabledTracedWithContext :: [Trace.TraceFrame] -> TracedNative -> Env -> Int -> SolverState -> Pred -> Term -> InstrumentedSearch
evalTabledTracedWithContext callers solveNative env fuel st0 p goal
  | any (isConstrained store0) callVars = plain st0
  | otherwise = case Map.lookup callKey (ssTables st0) of
      Just te
        | teComplete te -> [Right BranchExhausted | teTruncated te] ++ consumeAnswers st0 (teAnswers te)
        | otherwise -> Right (ConsumedIncomplete callKey) : consumeAnswers st0 (teAnswers te)
      Nothing -> fixpoint (case deltaClauses of Just _ -> True; Nothing -> False)
        (0 :: Int) (ssTables st0) [] Set.empty []
  where
    store0 = ssStore st0
    s0 = stSubst store0
    (callKey, callVars) = canonicalize s0 goal
    argsW = case deepWalk s0 goal of Compound _ as -> as; _ -> []
    plain st = evalClausesTraced callers solveNative env fuel st p goal argsW

    -- A delta is sound only when removing an old derivation cannot change a
    -- later call's behaviour. Keep the initial fast path deliberately narrow:
    -- one self-call first in a clause, exactly the current variant, followed
    -- by acyclic positive goals with no declared contracts, effects or CLP.
    -- In particular this excludes mutual/nonlinear recursion and all control
    -- constructs; their ordering, errors and cuts still use the old evaluator.
    deltaClauses
      | not (safeContract p) || inferredCommit = Nothing
      | otherwise = fmap (map fst . filter snd) (mapM classifyClause candidates)
      where
        inferredCommit = Contracts.commitsAfterSuccess p Nothing argsW
        candidates = candidateClauses p
          (if predIsIndexed (envProg env) p then map indexKey argsW else [])
        classifyClause ci =
          let cl = predClauses p IM.! ci
           in case clauseBody cl of
                recursive : rest
                  | functorOf recursive == Just (predKey p) ->
                      if all (safeGoal (Set.singleton (predKey p))) rest && sameVariant cl recursive
                        then Just (ci, True)
                        else Nothing
                body
                  | all (safeGoal (Set.singleton (predKey p))) body -> Just (ci, False)
                  | otherwise -> Nothing
        sameVariant cl recursive =
          let base = ssFresh st0
           in case storeUnify store0 goal (renameTerm base (clauseHead cl)) of
                Left _ -> False
                Right Nothing -> True -- This clause cannot contribute.
                Right (Just store) ->
                  let s = stSubst store
                   in fst (canonicalize s (normArithTerm s (renameTerm base recursive))) == callKey
        safeContract predicate =
          null (predDecls predicate)
            && not (predIsUnsafe (envProg env) predicate)
            && not (predIsDynamic (envProg env) predicate)
        safeGoal _ (Atom name) | name `elem` ["true", "fail", "false"] = True
        safeGoal _ (Compound "unify" [_, _]) = True
        safeGoal seen term = case functorOf term of
          Just key@(name, arity)
            | builtinDet name arity == Nothing && Set.notMember key seen ->
                case lookupPred key (envProg env) of
                  Just predicate ->
                    safeContract predicate
                      && all (all (safeGoal (Set.insert key seen)) . clauseBody)
                        (IM.elems (predClauses predicate))
                  Nothing -> False
          _ -> False

    fixpoint useDelta iteration tables answers answerSet delta =
      let visible = if useDelta then delta else answers
          st1 = st0 {ssTables = Map.insert callKey (TableEntry False False visible answerSet) tables}
          instrumented = case (useDelta && iteration > 0, deltaClauses) of
            (True, Just recursive) ->
              let base = ssFresh st1
               in if fuel <= 0 then [Right BranchExhausted] else
                    consumeMarkersTraced base (altsTraced
                      [tryClauseTraced callers solveNative env fuel st1 base p goal ci | ci <- recursive])
            _ -> evalClausesTraced callers solveNative env fuel st1 p goal argsW
          -- A constrained answer restarts plain evaluation immediately in
          -- the general algorithm. Do not force later producer retries just
          -- to obtain their trace log: that would change finite-prefix
          -- behavior. The positive delta proof excludes constrained answers;
          -- retain its full-round issue/dependency check before any restart.
          (logs, items, earlyUnsafe) = collectRound useDelta instrumented
          founds = [stf | Found stf <- items]
          extracted = map extract founds
          unsafe = earlyUnsafe || any (\(_, _, _, bad) -> bad) extracted
          fresh = dedup answerSet [(a, n, o) | (a, n, o, _) <- extracted]
          answers' = answers ++ fresh
          answerSet' = foldl' (\acc (a, _, _) -> Set.insert a acc) answerSet fresh
          deps = nub [k | ConsumedIncomplete k <- items, k /= callKey]
          others = [i | i@(BranchError _) <- items] ++ [BranchExhausted | any isExhausted items]
          completed = Map.unions (Map.filter teComplete tables : [Map.filter teComplete (ssTables stf) | stf <- founds])
          tables' = Map.union completed (Map.delete callKey tables)
          converged = null fresh
          gaveUp = iteration >= Reference.maxTableIterations
          -- Resource exhaustion can make an otherwise independent base clause
          -- observable on every round. Restart with the general algorithm
          -- rather than silently dropping such an issue on subsequent rounds.
          deltaIssue = useDelta && (not (null deps) || not (null others))
       in if deltaIssue
            then logs ++ fixpoint False 0 (ssTables st0) [] Set.empty []
            else if unsafe
            then logs ++ plain st0
            else
              if converged || gaveUp
                then
                  let tables'' =
                        if null deps
                          then Map.insert callKey (TableEntry True (not converged) answers' answerSet') tables'
                          else tables'
                      stC = st0 {ssTables = tables''}
                   in logs ++ map (Right . ConsumedIncomplete) deps
                        ++ map Right others
                        ++ [Right BranchExhausted | gaveUp]
                        ++ consumeAnswers stC answers'
                else logs ++ fixpoint useDelta (iteration + 1) tables' answers' answerSet' fresh

    collectRound full = go [] []
      where
        go logs items [] = (reverse logs, reverse items, False)
        go logs items (Left event : rest) = go (Left event : logs) items rest
        go logs items (Right item : rest) = case item of
          Found state
            | not full, (_, _, _, True) <- extract state ->
                (reverse logs, reverse (item : items), True)
          _ -> go logs (item : items) rest

    extract stf =
      let sf = stSubst (ssStore stf)
          (ans, vs) = canonicalize sf goal
          bad = any (isConstrained (ssStore stf)) vs
          out = reverse (take (ssOutLen stf - ssOutLen st0) (ssOutput stf))
       in (ans, length vs, out, bad)

    dedup _ [] = []
    dedup seen ((a, n, o) : rest)
      | Set.member a seen = dedup seen rest
      | otherwise = (a, n, o) : dedup (Set.insert a seen) rest

    consumeAnswers st answers =
      map Right $ alts
        [ let ans' = instantiate (ssFresh st) ans
              st' = foldl' (flip emit) st {ssFresh = ssFresh st + n} out
           in case storeUnify (ssStore st') goal ans' of
                Left err -> [BranchError err]
                Right Nothing -> []
                Right (Just store) -> [Found st' {ssStore = store}]
        | (ans, n, out) <- answers
        ]
