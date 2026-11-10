{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

-- | The clause compiler: whole predicates to native code, increments 1 and 2 of
-- @docs/2026-11-06-CLAUSE-COMPILER.md@.
--
-- A unit is an entry predicate and every predicate it reaches. Each
-- predicate is compiled clause by clause: head matching in read and write
-- mode, inline arithmetic, comparisons, type and groundness tests, structural
-- equality and disequality, cuts, @once@, @not@, unification with a term, and
-- calls to the unit's other predicates. Clause variables live in an
-- environment frame on a native stack (not the C stack), and a call stores
-- its return address in the callee's frame.
--
-- Exclusive predicates commit to the first clause whose head and leading
-- guards hold. Non-exclusive predicates use shallow head/guard matching and
-- link their native frame into the choice-point chain (@stateBIdx@) when a
-- non-final clause's head and leading guards succeed.
module Infera.Core.Jit.Clause
  ( UnitPlan (..),
    admitClauseUnit,
    planClauseUnit,
  )
where

import Control.Monad (forM, forM_, unless, when, zipWithM_)
import Control.Monad.State.Strict
import Data.Bits (complement, (.|.))
import Data.Int (Int64)
import Data.List (group, nub, sortOn)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Infera.Core.Jit.Exclusive
import Infera.Core.Jit.IR
import Infera.Core.Store (Symbols, atmWord, chrWord, funWord, groundBit, internAtom, internFunctor, intWord, tagAtm, tagBox, tagChr, tagInt, tagRef, tagStr)
import Infera.Error (PredKey)
import qualified Infera.Infer as I
import qualified Infera.Program as P
import qualified Infera.Syntax as S

data UnitPlan = UnitPlan
  { upUnit :: JitUnit,
    -- | argument slots the unit's calls use (the largest arity)
    upArgSlots :: Int,
    upPreds :: [PredKey],
    -- | True when native choice-point enumeration is guaranteed not to hit
    -- a mid-enumeration interpreter rerun once preflight checks pass
    upRerunFree :: !Bool
  }

-- | Compile the unit rooted at a predicate, or say why not. The second
-- argument tells whether a goal name and arity is a builtin of the core
-- compiler (anything else that names a program predicate is a call).
planClauseUnit :: Symbols -> (String -> Int -> Bool) -> P.Program -> PredKey -> IO (Either String UnitPlan)
planClauseUnit syms isBuiltin prog entry = case gatherUnit isBuiltin prog entry of
  Left why -> pure (Left why)
  Right preds -> do
    let clausesOf k = maybe [] (IM.elems . P.predClauses) (P.lookupPred k prog)
        allClauses = [cl | (k, _) <- preds, cl <- clausesOf k]
        terms = concat [S.clauseHead c : concatMap flatten (S.clauseBody c) | c <- allClauses]
        dataTerms = concat [headArgs c ++ concatMap goalDataTerms (concatMap flatten (S.clauseBody c)) | c <- allClauses]
        goalDataTerms = \case
          S.Compound "unify" [a, b] -> [a, b]
          S.Compound "equiv" [a, b] -> [a, b]
          S.Compound "neq" [a, b] -> [a, b]
          g
            | isInlineGuard g || g == S.Atom "!" -> []
            | otherwise -> callArgs g
    atoms <- forM (nub (concatMap atomsIn terms)) $ \a -> (,) a . fromIntegral . atmWord <$> internAtom syms a
    funs <- forM (nub (concatMap funsIn terms)) $ \(f, n) -> do
      fid <- internFunctor syms f n
      pure ((f, n), fromIntegral (funWord fid n))
    let env = CEnv (M.fromList atoms) (M.fromList funs)
        idx = M.fromList (zip (map fst preds) [0 :: Int ..])
    pure $ do
      let sels = [(k, selectOrNondet p (clausesOf k)) | (k, p) <- preds]
          selMap = M.fromList sels
          unitCanReclaimH =
            null (concatMap funsIn dataTerms)
              && all (selExclusive . snd) sels
              && not (any (\cl -> countControlTemps cl > 0) allClauses)
          freshOutMap = inferFreshOutArgs preds clausesOf
          (choiceSafe, needIntMap, needGndMap) = inferChoiceNeeds env preds clausesOf selMap
      bodies <- forM (zip [0 :: Int ..] sels) $ \(i, (k, sel)) ->
        compilePred env idx unitCanReclaimH (M.findWithDefault Set.empty k freshOutMap) i k (clausesOf k) sel
      let entrySel = case sels of
            (_, sel) : _ -> sel
            [] -> Selection True [] [] []
          entryArity = snd entry
          entryNeedInt = Set.toAscList (M.findWithDefault Set.empty entry needIntMap `Set.difference` Set.fromList (selInt entrySel))
          entryNeedGnd =
            Set.toAscList
              ( M.findWithDefault Set.empty entry needGndMap
                  `Set.difference` Set.fromList (selInt entrySel ++ entryNeedInt ++ selGround entrySel)
              )
          checkedEntryArgs = Set.fromList (selInt entrySel ++ entryNeedInt ++ selGround entrySel ++ entryNeedGnd)
          otherEntryArgs = [p | p <- [0 .. entryArity - 1], Set.notMember p checkedEntryArgs]
          choiceChecks =
            [ JLoadImm RT0 RState stateAllowChoicesIdx,
              JBranchImm JEq RT0 0 "choices_checked"
            ]
              ++ concat [intCheck p "no_choices" | p <- entryNeedInt]
              ++ concat [groundCheck ("cpre_" ++ show p) p "no_choices" | p <- entryNeedGnd]
              ++ concat [argSafeCheck ("asafe_" ++ show p) p "no_choices" | p <- otherEntryArgs]
              ++ [ JJump "choices_checked",
                   JLabel "no_choices",
                   JMovImm RT0 0,
                   JStoreImm RT0 RState stateAllowChoicesIdx,
                   JLabel "choices_checked"
                 ]
          maxArity = maximum (1 : map (snd . fst) preds)
          preflight =
            [ JLoadImm RT0 RState stateBIdx,
              JBranchImm JNe RT0 0 "resume",
              JLoadImm RSP RState stateNStackBaseIdx,
              JMov RE RSP
            ]
              ++ concat [intCheck p "decline" | p <- selInt entrySel]
              ++ concat [groundCheck ("pre_" ++ show p) p "decline" | p <- selGround entrySel]
              ++ choiceChecks
              ++ [JLoadLabel RT7 "unit_done", JJump (predLabel 0)]
          exits =
            [ JLabel "resume",
              JMov RE RT0,
              JLoadImm RT7 RE frameNextAlt,
              JJumpReg RT7,
              JLabel "unit_done",
              JLoadImm RT0 RState stateBIdx,
              JBranchImm JEq RT0 0 "unit_ok",
              JLoadImm RT1 RState stateAllowChoicesIdx,
              JBranchImm JEq RT1 0 "need_choices",
              JLabel "unit_ok",
              JReturn jitSuccess,
              JLabel "need_choices",
              JReturn 7,
              JLabel "fail",
              JLoadImm RT0 RState stateBIdx,
              JBranchImm JEq RT0 0 "fail_exit",
              JMov RE RT0,
              JLoadImm RT7 RE frameNextAlt,
              JJumpReg RT7,
              JLabel "fail_exit",
              JReturn jitFailure,
              JLabel "decline",
              JReturn jitDeclined,
              JLabel "bailout",
              JReturn jitBailout,
              JLabel "rerun",
              JReturn jitError,
              JLabel "exhausted",
              JReturn jitExhausted,
              JLabel "stackfull",
              JReturn jitStackFull
            ]
              ++ unifySlowOps
              ++ gndClearOps
          rerunFree = choiceSafe && not (any hasDeepNonGroundTerm terms)
      pure (UnitPlan (JitUnit (preflight ++ concat bodies ++ exits)) maxArity (map fst preds) rerunFree)

-- | Whether a term has nested compound structures of depth >= 3 containing
-- variables that could trigger a deep occurs-check or deep structure
-- unification bailout in 'unifySlowOps'.
hasDeepNonGroundTerm :: S.Term -> Bool
hasDeepNonGroundTerm = \case
  S.Compound _ as -> any (\a -> compDepth a >= 2 && not (null (termVarIds a))) as
  _ -> False
  where
    compDepth :: S.Term -> Int
    compDepth = \case
      S.Compound _ bs -> 1 + maximum (0 : map compDepth bs)
      _ -> 0

-- | Contiguous constant-key groups at argument 0 when a predicate of arity >= 2
-- has >= 4 distinct constants and every clause has an immediate constant at
-- argument 0 grouped contiguously by constant key. Returns @(sortedFirstPairs, groupLastSet)@.
arg0ConstGroups :: CEnv -> Int -> [S.Clause] -> Maybe ([(Int64, Int)], Set.Set Int)
arg0ConstGroups env arity clauses
  | arity < 2 = Nothing
  | otherwise = do
      cws <- mapM (arg0Const env) clauses
      let gs = group cws
          heads = [cw | (cw : _) <- gs]
      if length gs >= 4 && length (nub heads) == length heads
        then
          let lens = map length gs
              starts = init (scanl (+) 0 lens)
              ends = [s + len - 1 | (s, len) <- zip starts lens]
           in Just (sortOn fst (zip heads starts), Set.fromList ends)
        else Nothing

-- | Infer which arguments of each predicate in the unit must be integers or
-- ground at entry so that no clause can evaluate an unbound variable or trigger
-- a read-only / non-ground bailout during native choice enumeration.
inferChoiceNeeds ::
  CEnv ->
  [(PredKey, P.Pred)] ->
  (PredKey -> [S.Clause]) ->
  M.Map PredKey Selection ->
  (Bool, M.Map PredKey (Set.Set Int), M.Map PredKey (Set.Set Int))
inferChoiceNeeds env preds clausesOf selMap = go True initInt initGnd
  where
    keys = map fst preds
    hasArg0Switch k = case arg0ConstGroups env (snd k) (clausesOf k) of
      Just _ -> True
      Nothing -> False
    initInt = M.fromList [(k, Set.fromList (maybe [] selInt (M.lookup k selMap))) | k <- keys]
    initGnd =
      M.fromList
        [ ( k,
            Set.fromList
              ( maybe [] selGround (M.lookup k selMap)
                  ++ [0 | hasArg0Switch k]
                  ++ [pos | Just sel <- [M.lookup k selMap], set <- selReadOnly sel, (pos, _) <- Set.toList set]
              )
          )
          | k <- keys
        ]
    go !ok0 iMap gMap =
      let stepPred k =
            let cls = clausesOf k
                res = map (clauseNeeds iMap gMap) cls
                okP = all (\(b, _, _) -> b) res
                is = [x | (_, x, _) <- res]
                gs = [y | (_, _, y) <- res]
             in ( okP,
                  Set.union (M.findWithDefault Set.empty k iMap) (Set.unions is),
                  Set.union (M.findWithDefault Set.empty k gMap) (Set.unions gs)
                )
          nextPairs = [(k, stepPred k) | k <- keys]
          ok' = ok0 && all (\(_, (b, _, _)) -> b) nextPairs
          iMap' = M.fromList [(k, is) | (k, (_, is, _)) <- nextPairs]
          gMap' = M.fromList [(k, gs) | (k, (_, _, gs)) <- nextPairs]
       in if iMap' == iMap && gMap' == gMap then (ok', iMap, gMap) else go ok' iMap' gMap'

    clauseNeeds iMap gMap cl =
      let hArgs = headArgs cl
          varOwner =
            M.fromListWith
              (\_ first -> first)
              [(v, (i, isPlainVar a)) | (i, a) <- zip [0 :: Int ..] hArgs, v <- termVarIds a]
          isPlainVar (S.Var _) = True
          isPlainVar _ = False
          needIntVar bound v (!ok, accI, accG)
            | Set.member v bound = (ok, accI, accG)
            | Just (i, True) <- M.lookup v varOwner = (ok, Set.insert i accI, accG)
            | Just (i, False) <- M.lookup v varOwner = (False, accI, Set.insert i accG)
            | otherwise = (False, accI, accG)
          needGndVar bound v (!ok, accI, accG)
            | Set.member v bound = (ok, accI, accG)
            | Just (i, _) <- M.lookup v varOwner = (ok, accI, Set.insert i accG)
            | otherwise = (False, accI, accG)
          walkGoals _ !ok accI accG [] = (ok, accI, accG)
          walkGoals bound !ok accI accG (g : gs) = case g of
            S.Compound "is" [lhs, rhs] ->
              let (ok', accI', accG') = foldr (needIntVar bound) (ok, accI, accG) (termVarIds rhs)
                  bound' = Set.union bound (Set.fromList (termVarIds lhs))
               in walkGoals bound' ok' accI' accG' gs
            S.Compound op [a, b] | op `elem` ["gt", "lt", "gte", "lte"] ->
              let (ok', accI', accG') = foldr (needIntVar bound) (ok, accI, accG) (termVarIds a ++ termVarIds b)
                  bound' = Set.union bound (Set.fromList (termVarIds a ++ termVarIds b))
               in walkGoals bound' ok' accI' accG' gs
            S.Compound op [a, b] | op `elem` ["neq", "equiv"] ->
              let bothVars = isVarTerm a && isVarTerm b
                  (ok', accI', accG') = foldr (needGndVar bound) (ok && not bothVars, accI, accG) (termVarIds a ++ termVarIds b)
               in walkGoals bound ok' accI' accG' gs
            S.Compound "is_int" [a] ->
              let hasCompoundHeadVar = any (\v -> Set.notMember v bound && case M.lookup v varOwner of Just (_, False) -> True; _ -> False) (termVarIds a)
               in walkGoals bound (ok && not hasCompoundHeadVar) accI accG gs
            S.Compound "ground" [a] ->
              let (ok', accI', accG') = foldr (needGndVar bound) (ok, accI, accG) (termVarIds a)
               in walkGoals bound ok' accI' accG' gs
            S.Compound "unify" [a, b] ->
              let vs = Set.fromList (termVarIds a ++ termVarIds b)
                  bound' =
                    if all (`Set.member` bound) (termVarIds a) || all (`Set.member` bound) (termVarIds b)
                      then Set.union bound vs
                      else bound
               in walkGoals bound' ok accI accG gs
            S.Compound "once" [inner] ->
              let (ok', accI', accG') = walkGoals bound ok accI accG (flatten inner)
               in walkGoals bound ok' accI' accG' gs
            S.Compound "not" [inner] ->
              let (ok', accI', accG') = walkGoals bound ok accI accG (flatten inner)
               in walkGoals bound ok' accI' accG' gs
            _ ->
              let ck = case g of
                    S.Atom f -> (f, 0)
                    S.Compound f as -> (f, length as)
                    _ -> ("", 0)
                  cArgs = callArgs g
                  calleeInt = M.findWithDefault Set.empty ck iMap
                  calleeGnd = M.findWithDefault Set.empty ck gMap
                  (ok', accI', accG') =
                    foldr
                      ( \(j, arg) (okAcc, ai, ag) ->
                          if Set.member j calleeInt
                            then case arg of
                              S.IntLit _ -> (okAcc, ai, ag)
                              S.Var v -> needIntVar bound v (okAcc, ai, ag)
                              _ -> foldr (needGndVar bound) (False, ai, ag) (termVarIds arg)
                            else
                              if Set.member j calleeGnd
                                then foldr (needGndVar bound) (okAcc && not (any (< 0) (allVarsIn arg)), ai, ag) (termVarIds arg)
                                else (okAcc, ai, ag)
                      )
                      (ok, accI, accG)
                      (zip [0 :: Int ..] cArgs)
                  bound' = Set.union bound (Set.fromList (concatMap termVarIds cArgs))
               in walkGoals bound' ok' accI' accG' gs
       in walkGoals Set.empty True Set.empty Set.empty (concatMap flatten (S.clauseBody cl))

-- | Greatest-fixpoint analysis for internal predicates (@pIx > 0@): an argument
-- position @(k, i)@ is 'FreshOut' when every call site to @k@ in the unit
-- passes a fresh, unseen variable (or forwards a 'FreshOut' head variable of
-- the caller before it has been used anywhere else).
inferFreshOutArgs :: [(PredKey, P.Pred)] -> (PredKey -> [S.Clause]) -> M.Map PredKey (Set.Set Int)
inferFreshOutArgs preds clausesOf = go initMap
  where
    internalKeys = map fst (drop 1 preds)
    hasCalls = Set.fromList [ck | (k, _) <- preds, cl <- clausesOf k, g <- concatMap goalsIn (S.clauseBody cl), let ck = goalKey g, ck `elem` internalKeys]
    initMap =
      M.fromList
        [ (k, if Set.member k hasCalls then Set.fromList [0 .. snd k - 1] else Set.empty)
          | k <- internalKeys
        ]
    goalKey = \case
      S.Atom f -> (f, 0)
      S.Compound f as -> (f, length as)
      _ -> ("", -1)
    go cur =
      let next = foldr (checkClause cur) cur [(k, cl) | (k, _) <- preds, cl <- clausesOf k]
       in if next == cur then cur else go next
    checkClause cur (callerKey, cl) acc =
      let hArgs = headArgs cl
          callerFresh = M.findWithDefault Set.empty callerKey cur
          headVarCount v = length [u | a <- hArgs, u <- termVarIds a, u == v]
          freshHeadVars =
            Set.fromList
              [ v
                | (i, S.Var v) <- zip [0 :: Int ..] hArgs,
                  v >= 0,
                  Set.member i callerFresh,
                  headVarCount v == 1
              ]
          seen0 = Set.fromList (concatMap termVarIds hArgs) `Set.difference` freshHeadVars
          walk seen m [] = (seen, m)
          walk seen m (g : gs) = case g of
            S.Compound "once" [inner] ->
              let (seen', m') = walk seen m (flatten inner)
               in walk seen' m' gs
            S.Compound "not" [inner] ->
              let (seen', m') = walk seen m (flatten inner)
               in walk seen' m' gs
            _
              | isInlineGuard g || g == S.Atom "!" ->
                  walk (Set.union seen (Set.fromList (termVarIds g))) m gs
              | S.Compound "unify" [a, b] <- g ->
                  walk (Set.union seen (Set.fromList (termVarIds a ++ termVarIds b))) m gs
              | otherwise ->
                  let ck = goalKey g
                      cArgs = callArgs g
                      argVarCount v = length [u | a <- cArgs, u <- termVarIds a, u == v]
                      okAt arg = case arg of
                        S.Var v | v < 0 -> True
                        S.Var v -> Set.notMember v seen && argVarCount v == 1
                        _ -> False
                      keep = Set.fromList [j | (j, a) <- zip [0 :: Int ..] cArgs, okAt a]
                      m' = M.adjust (`Set.intersection` keep) ck m
                      seen' = Set.union seen (Set.fromList (concatMap termVarIds cArgs))
                   in walk seen' m' gs
       in snd (walk seen0 acc (concatMap flatten (S.clauseBody cl)))

-- | Whether a predicate may root a unit: everything it reaches is in the
-- fragment. Cheap (no selection proofs, no code), so the loader asks it of
-- every predicate and leaves the rest to the first call.
admitClauseUnit :: (String -> Int -> Bool) -> P.Program -> PredKey -> Either String ()
admitClauseUnit isBuiltin prog entry = () <$ gatherUnit isBuiltin prog entry

-- | Every predicate the entry reaches, entry first, or why one is outside
-- the fragment.
gatherUnit :: (String -> Int -> Bool) -> P.Program -> PredKey -> Either String [(PredKey, P.Pred)]
gatherUnit isBuiltin prog entry = gather [entry] []
  where
    gather [] done = Right (reverse done)
    gather (k : queue) done
      | k `elem` map fst done = gather queue done
      | otherwise = do
          p <- maybe (Left (show k ++ " undefined")) Right (P.lookupPred k prog)
          admissible k p
          let callees = [c | cl <- IM.elems (P.predClauses p), g <- concatMap goalsIn (S.clauseBody cl), Just c <- [callKey g]]
          gather (queue ++ callees) ((k, p) : done)
    admissible k p
      | not (null (P.predDecls p)) = Left (show k ++ " has declared contracts")
      | P.predIsTabled prog p = Left (show k ++ " is tabled")
      | P.nameHasFlag prog (fst k) S.FlagDynamic = Left (show k ++ " is dynamic")
      | snd k > 8 = Left (show k ++ " has more than 8 arguments")
      | IM.null (P.predClauses p) = Left (show k ++ " has no clauses")
      | IM.size (P.predClauses p) > 128 = Left (show k ++ " has more than 128 clauses")
      | k /= entry && isTrmcCallee k p = Left (show k ++ " is a TRMC list kernel")
      | otherwise = mapM_ (admissibleClause k) (IM.elems (P.predClauses p))
    isTrmcCallee (name, arity) p =
      arity == 3
        && IM.size (P.predClauses p) == 2
        && P.sigDet (P.predInferred p) == S.Det
        && any isTrmcClause (IM.elems (P.predClauses p))
      where
        isTrmcClause cl = case (headArgs cl, reverse (concatMap flatten (S.clauseBody cl))) of
          (hArgs@(_ : _), S.Compound rName rArgs : _)
            | rName == name && length rArgs == arity,
              S.Compound "cons" [_, _] <- last hArgs ->
                True
          _ -> False
    admissibleClause k cl = do
      unless (all headTermOk (headArgs cl)) (Left (show k ++ ": head outside the fragment"))
      forM_ (concatMap flatten (S.clauseBody cl)) $ \g ->
        unless (goalOk g) (Left (show k ++ ": goal outside the fragment: " ++ take 60 (show g)))
    goalOk g = case g of
      S.Atom "true" -> True
      S.Atom "fail" -> True
      S.Atom "false" -> True
      S.Atom "!" -> True
      S.Compound "$cut" [S.IntLit _] -> True
      S.Compound "is" [l, e] -> termOk l && exprOk e
      S.Compound op [a, b] | op `elem` ["gt", "lt", "gte", "lte"] -> exprOk a && exprOk b
      S.Compound "neq" [a, b] -> atomicOk a && atomicOk b
      S.Compound "equiv" [a, b] -> (atomicOk a && atomicOk b) || (isVarTerm a && groundTermOk b) || (groundTermOk a && isVarTerm b)
      S.Compound "unify" [a, b] -> termOk a && termOk b
      S.Compound op [x] | op `elem` ["is_int", "is_atom", "is_char", "var", "nonvar", "ground"] -> termOk x
      S.Compound "once" [inner] -> all goalOk (flatten inner)
      S.Compound "not" [inner] -> all goalOk (flatten inner)
      _ -> case callKey g of
        Just _ -> all termOk (callArgs g)
        Nothing -> False
    callKey g = case g of
      S.Atom f | not (isBuiltin f 0), userPred (f, 0) -> Just (f, 0)
      S.Compound f as | not (isBuiltin f (length as)), userPred (f, length as) -> Just (f, length as)
      _ -> Nothing
    userPred k = case P.lookupPred k prog of
      Just _ -> not (P.nameHasFlag prog (fst k) S.FlagDynamic)
      Nothing -> False

-- ─── Terms ───────────────────────────────────────────────────────────────────

flatten :: S.Term -> [S.Term]
flatten = \case
  S.Compound "," [a, b] -> flatten a ++ flatten b
  t -> [t]

goalsIn :: S.Term -> [S.Term]
goalsIn = \case
  S.Compound "," [a, b] -> goalsIn a ++ goalsIn b
  S.Compound "once" [g] -> goalsIn g
  S.Compound "not" [g] -> goalsIn g
  t -> [t]

headArgs :: S.Clause -> [S.Term]
headArgs cl = case S.clauseHead cl of
  S.Compound _ as -> as
  _ -> []

callArgs :: S.Term -> [S.Term]
callArgs = \case
  S.Compound _ as -> as
  _ -> []

arithNames :: [(String, Int)]
arithNames = [("plus", 2), ("minus", 2), ("mul", 2), ("div", 2), ("mod", 2), ("^", 2), ("neg", 1), ("abs", 1), ("min", 2), ("max", 2)]

fits :: Integer -> Bool
fits k = k >= -(2 ^ (60 :: Int)) && k < 2 ^ (60 :: Int)

-- | Terms in clause heads: 'compileHeadArg' in 'Infera.Core.Compile' compiles
-- every compound term in a clause head as 'PStruct' (never 'PArith'), so
-- functors such as @neg/1@ in @d (neg U) X (neg DU)@ are ordinary structures.
headTermOk :: S.Term -> Bool
headTermOk = \case
  S.Var _ -> True
  S.Atom _ -> True
  S.IntLit k -> fits k
  S.CharLit _ -> True
  S.Compound f as -> f /= "$path" && all headTermOk as
  _ -> False

-- | Terms native code builds in body goals: variables, immediate constants,
-- and structures of them. An arithmetic functor as data in a body argument is
-- evaluated by the interpreter in some positions ('PArith'), so it is left out.
termOk :: S.Term -> Bool
termOk = \case
  S.Var _ -> True
  S.Atom _ -> True
  S.IntLit k -> fits k
  S.CharLit _ -> True
  S.Compound f as -> (f, length as) `notElem` arithNames && f /= "$path" && all termOk as
  _ -> False

groundTermOk :: S.Term -> Bool
groundTermOk t = termOk t && null (allVarsIn t)

isVarTerm :: S.Term -> Bool
isVarTerm = \case
  S.Var v -> v >= 0
  _ -> False

exprOk :: S.Term -> Bool
exprOk = \case
  S.Var _ -> True
  S.IntLit k -> fits k
  S.Compound op [a, b] | op `elem` ["plus", "minus", "mul", "mod"] -> exprOk a && exprOk b
  _ -> False

atomicOk :: S.Term -> Bool
atomicOk = \case
  S.Var _ -> True
  S.Atom _ -> True
  S.IntLit k -> fits k
  S.CharLit _ -> True
  _ -> False

atomsIn :: S.Term -> [String]
atomsIn = \case
  S.Atom a -> [a]
  S.Compound _ as -> concatMap atomsIn as
  _ -> []

funsIn :: S.Term -> [(String, Int)]
funsIn = \case
  S.Compound f as -> (f, length as) : concatMap funsIn as
  _ -> []

termVarIds :: S.Term -> [S.VarId]
termVarIds = \case
  S.Var v | v >= 0 -> [v]
  S.Compound _ as -> concatMap termVarIds as
  _ -> []

allVarsIn :: S.Term -> [S.VarId]
allVarsIn = \case
  S.Var v -> [v]
  S.Compound _ as -> concatMap allVarsIn as
  _ -> []

data CEnv = CEnv
  { ceAtoms :: M.Map String Int64,
    ceFuns :: M.Map (String, Int) Int64
  }

constWord :: CEnv -> S.Term -> Maybe Int64
constWord env = \case
  S.Atom a -> M.lookup a (ceAtoms env)
  S.IntLit k | fits k -> Just (fromIntegral (intWord (fromInteger k)))
  S.CharLit c -> Just (fromIntegral (chrWord (fromEnum c)))
  _ -> Nothing

funW :: CEnv -> String -> Int -> Int64
funW env f n = M.findWithDefault (error ("Clause.funW: " ++ f)) (f, n) (ceFuns env)

-- ─── Selection ───────────────────────────────────────────────────────────────

-- | How a predicate's clauses are selected: either mutually exclusive
-- ('selExclusive' = True, committing after head and guard prefix) or
-- nondeterministic ('selExclusive' = False, pushing a native choice frame
-- when a non-final clause's head and guard prefix succeed).
data Selection = Selection
  { selExclusive :: !Bool,
    selInt :: [Int],
    selGround :: [Int],
    selReadOnly :: [Set.Set (Int, [Int])]
  }

-- | Leading goals used by the static exclusivity proof.
isEarlyGuard :: S.Term -> Bool
isEarlyGuard = \case
  S.Atom "true" -> True
  S.Compound "is" _ -> True
  S.Compound op [_, _] -> op `elem` ["gt", "lt", "gte", "lte", "neq"]
  _ -> False

-- | Leading inline tests that bind no external variables and have at most
-- one solution; executed before pushing a native choice point.
isInlineGuard :: S.Term -> Bool
isInlineGuard = \case
  S.Atom "true" -> True
  S.Atom "fail" -> True
  S.Atom "false" -> True
  S.Compound "is" _ -> True
  S.Compound op [_, _] | op `elem` ["gt", "lt", "gte", "lte", "neq", "equiv"] -> True
  S.Compound op [_] | op `elem` ["is_int", "is_atom", "is_char", "var", "nonvar", "ground"] -> True
  S.Compound "not" [g] -> case flatten g of
    [single] -> isSimpleNegatable single
    _ -> False
  _ -> False

isSimpleNegatable :: S.Term -> Bool
isSimpleNegatable = \case
  S.Compound "equiv" [a, b] -> atomicOk a && atomicOk b
  S.Compound "neq" [a, b] -> atomicOk a && atomicOk b
  S.Compound op [_, _] | op `elem` ["gt", "lt", "gte", "lte"] -> True
  S.Compound op [_] | op `elem` ["is_int", "is_atom", "is_char", "var", "nonvar", "ground"] -> True
  _ -> False

guardPrefix :: S.Clause -> [S.Term]
guardPrefix = takeWhile isEarlyGuard . concatMap flatten . S.clauseBody

selectOrNondet :: P.Pred -> [S.Clause] -> Selection
selectOrNondet p clauses = case selection p clauses of
  Right sel -> sel
  Left _ -> Selection False [] [] (replicate (length clauses) Set.empty)

-- | Committing to clause @i@ after its head and guard prefix is safe when
-- every later clause @j@ cannot match then, and could not raise an error
-- the interpreter would raise before failing it.
selection :: P.Pred -> [S.Clause] -> Either String Selection
selection p clauses = do
  pairs <- forM [(i, j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1]] pair
  let ints = nub [x | (xs, _, _) <- pairs, x <- xs]
      grounds = nub [x | (_, xs, _) <- pairs, x <- xs]
      roMap = M.fromListWith Set.union [(i, paths) | (_, _, ros) <- pairs, (i, paths) <- ros]
      ro = [if i == n - 1 then Set.empty else M.findWithDefault Set.empty i roMap | i <- [0 .. n - 1]]
  pure (Selection True ints grounds ro)
  where
    n = length clauses
    key = P.predKey p
    arity = snd key
    inferred = P.predInferred p
    isDet = P.sigDet inferred == S.Det
    isDetOrSemidet = P.sigDet inferred `elem` [S.Det, S.Semidet]
    modes = map S.argMode (P.sigArgs inferred)
    isInput i = length modes /= arity || modes !! i /= S.ModeOut
    mask cl =
      let hd = case S.clauseHead cl of
            S.Compound f as -> S.Compound f [if isInput i then a else S.Var (-1) | (i, a) <- zip [0 ..] as]
            h -> h
       in S.Clause hd (guardPrefix cl) (S.clauseNVars cl)
    masked = map mask clauses
    switch = P.sigSwitch inferred
    commitsOnSuccess = P.sigDet inferred == S.Semidet && not (null switch) && all isInput switch
    extraIntArgs c1 c2 = case (evaluatedPaths c1, evaluatedPaths c2) of
      (Just ei, Just ej) ->
        let missing = Set.toList (ej `Set.difference` (ei `Set.union` intLitPaths c1))
         in if all (\(pos, sub) -> null sub && isInput pos) missing
              then Just (map fst missing)
              else Nothing
      _ -> Nothing
    headCannotBind cl roSet =
      let hvs = concatMap termVarIds (headArgs cl)
       in length hvs == length (nub hvs) && readOnlyPaths cl `Set.isSubsetOf` roSet
    pair (i, j)
      | (if isDet then headsExclusive arity ci cj else headsExclusive 1 ci cj) =
          Right ([], [], [(i, disjointPaths (if isDet then arity else 1) ci cj)])
      | laterRaisesNothingNew arity ci cj, Just ints <- extraIntArgs ci cj, clausesExclusive arity ci cj =
          let roSet = guardRoPaths ci
              gnd = if headCannotBind (clauses !! i) roSet then [] else guarded
           in Right (ints, gnd, [(i, roSet)])
      | isDetOrSemidet, laterRaisesNothingNew arity ci cj, evalSafe ci cj, Just ps <- I.exclusive ci cj, all isInput ps =
          Right ([], nub (ps ++ guarded), [(i, guardRoPaths ci)])
      | commitsOnSuccess, allGuards (clauses !! i) =
          Right ([], switch, [(i, Set.filter (\(pos, _) -> pos `elem` switch) (readOnlyPaths ci))])
      | otherwise = Left (show key ++ ": clauses " ++ show (i + 1) ++ " and " ++ show (j + 1) ++ " may both match")
      where
        ci = masked !! i
        cj = masked !! j
        guarded = case (evaluatedPaths ci, evaluatedPaths cj) of
          (Just ei, Just ej) -> nub (map fst (Set.toList (ei `Set.union` ej)))
          _ -> []
        guardRoPaths cl =
          let evalStructPaths = case evaluatedPaths cl of
                Just ep -> Set.fromList [(argI, take len sub) | (argI, sub) <- Set.toList ep, len <- [0 .. length sub - 1], not (null sub)]
                Nothing -> Set.empty
           in intLitPaths cl `Set.union` evalStructPaths
    allGuards cl = all isEarlyGuard (concatMap flatten (S.clauseBody cl))

-- | Minimal set of non-variable paths in @ci@ (and their ancestor paths) at
-- the first argument where @ci@ and @cj@ have disjoint shapes.
disjointPaths :: Int -> S.Clause -> S.Clause -> Set.Set (Int, [Int])
disjointPaths inCount ci cj =
  case [ps | (i, a, b) <- zip3 [0 .. inCount - 1] (headArgs ci) (headArgs cj), let ps = walk (i, []) a b, not (Set.null ps)] of
    ps : _ -> ps
    [] -> Set.empty
  where
    walk path a b = case (a, b) of
      (S.Var _, _) -> Set.empty
      (_, S.Var _) -> Set.empty
      (S.Compound f as, S.Compound g bs)
        | f == g && length as == length bs ->
            case [sub | (k, x, y) <- zip3 [1 ..] as bs, let sub = walk (fst path, snd path ++ [k]) x y, not (Set.null sub)] of
              sub : _ -> Set.insert path sub
              [] -> Set.empty
        | otherwise -> Set.singleton path
      _
        | shapesDisjoint (shapeOf a) (shapeOf b) -> Set.singleton path
        | otherwise -> Set.empty

-- | Paths in a head where the pattern is not a variable.
readOnlyPaths :: S.Clause -> Set.Set (Int, [Int])
readOnlyPaths cl = Set.fromList (concat [walk (i, []) a | (i, a) <- zip [0 ..] (headArgs cl)])
  where
    walk path = \case
      S.Var _ -> []
      S.Compound _ as -> path : concat [walk (fst path, snd path ++ [k]) a | (k, a) <- zip [1 ..] as]
      _ -> [path]

-- | Head variable paths, first occurrence.
varPaths :: S.Clause -> M.Map S.VarId (Int, [Int])
varPaths cl = M.fromListWith (\_ first -> first) (concat [walk (i, []) a | (i, a) <- zip [0 ..] (headArgs cl)])
  where
    walk path = \case
      S.Var v | v >= 0 -> [(v, path)]
      S.Compound _ as -> concat [walk (fst path, snd path ++ [k]) a | (k, a) <- zip [1 ..] as]
      _ -> []

intLitPaths :: S.Clause -> Set.Set (Int, [Int])
intLitPaths cl = Set.fromList (concat [walk (i, []) a | (i, a) <- zip [0 ..] (headArgs cl)])
  where
    walk path = \case
      S.IntLit _ -> [path]
      S.Compound _ as -> concat [walk (fst path, snd path ++ [k]) a | (k, a) <- zip [1 ..] as]
      _ -> []

-- | The head paths a clause's guard prefix evaluates (operands of @is@,
-- comparisons and @!=@), or 'Nothing' when it evaluates a variable that is
-- neither a head variable nor defined by an earlier @is@ (which raises
-- whenever it runs).
evaluatedPaths :: S.Clause -> Maybe (Set.Set (Int, [Int]))
evaluatedPaths cl = go Set.empty Set.empty (S.clauseBody cl)
  where
    paths = varPaths cl
    go _ acc [] = Just acc
    go defs acc (g : gs) = case g of
      S.Compound "is" [l, e] -> do
        acc' <- uses defs acc (termVarIds e)
        let defs' = case l of
              S.Var v | v >= 0, not (M.member v paths) -> Set.insert v defs
              _ -> defs
        acc'' <- case l of
          S.Var v | M.member v paths || Set.member v defs -> uses defs acc' [v]
          _ -> Just acc'
        go defs' acc'' gs
      S.Compound _ [a, b] -> uses defs acc (termVarIds a ++ termVarIds b) >>= \acc' -> go defs acc' gs
      _ -> go defs acc gs
    uses defs acc vs = foldl (\m v -> m >>= use defs v) (Just acc) vs
    use defs v acc
      | Set.member v defs = Just acc
      | Just path <- M.lookup v paths = Just (Set.insert path acc)
      | otherwise = Nothing

-- | Clause @j@'s prefix runs only after clause @i@'s head and prefix held,
-- so it raises nothing new when everything it evaluates was evaluated by
-- clause @i@ (an integer there, or clause @i@ would have stopped) or pinned
-- to an integer by clause @i@'s head.
evalSafe :: S.Clause -> S.Clause -> Bool
evalSafe ci cj = case (evaluatedPaths ci, evaluatedPaths cj) of
  (Just ei, Just ej) -> ej `Set.isSubsetOf` (ei `Set.union` intLitPaths ci)
  _ -> False

-- ─── Code generation ─────────────────────────────────────────────────────────

-- Frame layout, in words from RE:
--   0: caller's frame (RE)
--   1: return code address (RT7)
--   2: entry trail mark (RTR)
--   3: entry heap mark (RH)
--   4: entry choice frame pointer (B)
--   5: entry choice heap boundary (RHB)
--   6: next clause retry label (when this frame is on the B chain)
--   7: entry depth budget (RDepth)
--   8 .. 8 + savedArgs - 1: saved call arguments (for non-exclusive predicates)
--   varBase ..: clause variables, followed by temp blocks for once/not
frameLink, frameRet, frameTR, frameH, framePrevB, frameHB, frameNextAlt, frameDepth, frameHeader :: Int
frameLink = 0
frameRet = 1
frameTR = 2
frameH = 3
framePrevB = 4
frameHB = 5
frameNextAlt = 6
frameDepth = 7
frameHeader = 8

predLabel :: Int -> Label
predLabel i = "p" ++ show i

data GS = GS
  { gsNext :: !Int,
    gsVarBase :: !Int,
    gsTempBase :: !Int,
    gsFrameSize :: !Int,
    gsSeen :: !(Set.Set S.VarId),
    gsFree :: ![Reg],
    gsOps :: ![[JitOp]]
  }

type G = StateT GS (Either String)

emit :: [JitOp] -> G ()
emit ops = modify' (\s -> s {gsOps = ops : gsOps s})

slot :: S.VarId -> G Int
slot v = gets (\s -> gsVarBase s + v)

allocTempBlock :: G Int
allocTempBlock = do
  s <- get
  let b = gsTempBase s
  put s {gsTempBase = b + 5}
  pure b

newLabel :: String -> G Label
newLabel base = do
  s <- get
  put s {gsNext = gsNext s + 1}
  pure (base ++ "_" ++ show (gsNext s))

allocReg :: G Reg
allocReg = do
  s <- get
  case gsFree s of
    r : rest -> put s {gsFree = rest} >> pure r
    [] -> lift (Left "out of registers")

freeReg :: Reg -> G ()
freeReg r = modify' (\s -> s {gsFree = r : gsFree s})

isSeen :: S.VarId -> G Bool
isSeen v = gets (Set.member v . gsSeen)

markSeen :: S.VarId -> G ()
markSeen v = modify' (\s -> s {gsSeen = Set.insert v (gsSeen s)})

decline :: String -> G a
decline = lift . Left

-- | RT7 is the scratch register of these sequences; RT0..RT6 are allocated.
workRegs :: [Reg]
workRegs = [RT0, RT1, RT2, RT3, RT4, RT5, RT6]

runGen :: Int -> Int -> Int -> Int -> G () -> Either String ([JitOp], Int)
runGen next varBase tempBase frameSize g = do
  s <- execStateT g (GS next varBase tempBase frameSize Set.empty workRegs [])
  pure (concat (reverse (gsOps s)), gsNext s)

countControlTemps :: S.Clause -> Int
countControlTemps cl = sum (map countG (concatMap flatten (S.clauseBody cl)))
  where
    countG = \case
      S.Compound "once" [g] -> 1 + sum (map countG (flatten g))
      S.Compound "not" [g] -> case flatten g of
        [single] | isSimpleNegatable single -> 0
        inner -> 1 + sum (map countG inner)
      _ -> 0

-- | Extract the immediate constant word at argument 0 of a clause if present.
arg0Const :: CEnv -> S.Clause -> Maybe Int64
arg0Const env cl = case headArgs cl of
  a : _ -> constWord env a
  [] -> Nothing

-- | Emit a binary search dispatch tree over sorted @(constWord, clauseIndex)@
-- pairs against @RT0@, using @RT1@ as scratch.
emitConstBinSearch :: String -> [(Int64, Int)] -> (Int -> Label) -> Label -> [JitOp]
emitConstBinSearch base pairs targetLbl missLbl = go "root" pairs
  where
    go _ [] = [JJump missLbl]
    go _ [(cw, k)] =
      [ JMovImm RT1 cw,
        JBranchCmp JEq RT0 RT1 (targetLbl k),
        JJump missLbl
      ]
    go _ [(cw1, k1), (cw2, k2)] =
      [ JMovImm RT1 cw1,
        JBranchCmp JEq RT0 RT1 (targetLbl k1),
        JMovImm RT1 cw2,
        JBranchCmp JEq RT0 RT1 (targetLbl k2),
        JJump missLbl
      ]
    go tag xs =
      let mid = length xs `div` 2
          (left, rest) = splitAt mid xs
       in case rest of
            (cwMid, kMid) : right ->
              let rightLbl = base ++ "_" ++ tag ++ "_r"
               in [ JMovImm RT1 cwMid,
                    JBranchCmp JEq RT0 RT1 (targetLbl kMid),
                    JBranchCmp JGt RT0 RT1 rightLbl
                  ]
                    ++ go (tag ++ "l") left
                    ++ [JLabel rightLbl]
                    ++ go (tag ++ "r") right
            [] -> [JJump missLbl]

compilePred :: CEnv -> M.Map PredKey Int -> Bool -> Set.Set Int -> Int -> PredKey -> [S.Clause] -> Selection -> Either String [JitOp]
compilePred env idx unitCanReclaimH freshOutArgs pIx key clauses sel = do
  let lbl = predLabel pIx
      n = length clauses
      arity = snd key
      exclusive = selExclusive sel
      savedArgWords = if not exclusive && n > 1 then arity else 0
      varBase = frameHeader + savedArgWords
      maxVars = maximum (0 : map S.clauseNVars clauses)
      maxTemps = maximum (0 : map countControlTemps clauses)
      frameSize = varBase + maxVars + 5 * maxTemps
      clauseLbl k = lbl ++ "_c" ++ show k
      undoLbl k = lbl ++ "_u" ++ show k
      retryLbl k = lbl ++ "_r" ++ show k
      sharedUndoFailLbl = lbl ++ "_ufail"
      arg0SwitchInfo = arg0ConstGroups env arity clauses
      isArg0Switch = case arg0SwitchInfo of
        Just _ -> True
        Nothing -> False
      groupLastSet = case arg0SwitchInfo of
        Just (_, ends) -> ends
        Nothing -> Set.singleton (n - 1)
      saveArgsOps =
        concat
          [ [JLoadImm RT0 RArgs i, JStoreImm RT0 RE (frameHeader + i)]
            | i <- [if isArg0Switch then 1 else 0 .. savedArgWords - 1]
          ]
      loadArgsOps =
        concat
          [ [JLoadImm RT0 RE (frameHeader + i), JStoreImm RT0 RArgs i]
            | i <- [if isArg0Switch then 1 else 0 .. savedArgWords - 1]
          ]
      entry =
        [ JLabel lbl,
          -- RT7 holds the return address. Reserve 10 extra words above RSP for
          -- temporary register spills in unifyWords/not.
          JAddImm RT6 RSP (8 * (frameSize + 10)),
          JLoadImm RT5 RState stateNStackLimIdx,
          JBranchCmp JGt RT6 RT5 "stackfull",
          JAddImm RT6 RSP (8 * frameSize),
          JStoreImm RE RSP frameLink,
          JStoreImm RT7 RSP frameRet,
          JLoadImm RT0 RState stateBIdx,
          JStoreImm RT0 RSP framePrevB,
          JStoreImm RHB RSP frameHB,
          JMov RE RSP,
          JMov RSP RT6
        ]
          ++ concat [intCheck p "rerun" | p <- selInt sel]
          ++ concat [groundCheck (lbl ++ "_g" ++ show p) p "rerun" | p <- selGround sel]
          ++ ( if n > 1
                 then
                   [ JStoreImm RTR RE frameTR,
                     JStoreImm RH RE frameH,
                     JStoreImm RDepth RE frameDepth,
                     JMov RHB RH
                   ]
                     ++ saveArgsOps
                 else [JStoreImm RH RE frameH | unitCanReclaimH]
             )
          ++ ( case arg0SwitchInfo of
                 Just (sortedPairs, _) ->
                   [ JLoadImm RT0 RArgs 0,
                     JDeref RT0 RT0,
                     JTagOf RT1 RT0,
                     JBranchImm JEq RT1 (fromIntegral tagRef) "rerun"
                   ]
                     ++ emitConstBinSearch (lbl ++ "_bs") sortedPairs clauseLbl "fail"
                 Nothing -> []
             )
  blocks <- forM (zip [0 ..] clauses) $ \(k, cl) -> do
    let isLast = Set.member k groupLastSet
        goals = concatMap flatten (S.clauseBody cl)
        guardPred = if exclusive then isEarlyGuard else isInlineGuard
        (prefix, rest) = span guardPred goals
        remArgs = drop 1 (headArgs cl)
        -- When an arg0Switch clause has no guards and at most one remaining
        -- ground argument (or distinct first-time variables), matching remArgs
        -- cannot fail after binding, so no trail undo is needed on failure.
        remVars = concatMap termVarIds remArgs
        remNoUndoOnFail =
          isArg0Switch
            && null prefix
            && (all groundTermOk remArgs && length remArgs <= 1 || all isVarTerm remArgs && length remVars == length (nub remVars))
        arg0DirectCommit = remNoUndoOnFail && isLast
        headFailL
          | remNoUndoOnFail = if isLast then "fail" else clauseLbl (k + 1)
          | isArg0Switch && isLast = sharedUndoFailLbl
          | isLast = "fail"
          | otherwise = undoLbl k
        ro = selReadOnly sel !! k
        gndArgs = Set.fromList (selGround sel)
        tempBase = varBase + S.clauseNVars cl
    (ops, _) <- runGen 0 varBase tempBase frameSize $ do
      emit [JLabel (clauseLbl k)]
      when ((isLast && n > 1) || arg0DirectCommit) (emit [JLoadImm RHB RE frameHB])
      if isArg0Switch
        then
          zipWithM_
            (\i a -> matchArg env (Set.member i gndArgs) (Set.member i freshOutArgs) ro (i, []) a i headFailL Nothing)
            [1 ..]
            remArgs
        else
          zipWithM_
            ( \i a ->
                matchArg
                  env
                  (Set.member i gndArgs)
                  (Set.member i freshOutArgs)
                  ro
                  (i, [])
                  a
                  i
                  headFailL
                  (if i == 0 && not isLast then Just (clauseLbl (k + 1)) else Nothing)
            )
            [0 ..]
            (headArgs cl)
      mapM_ (compileGuard env headFailL) prefix
      unless (isLast || arg0DirectCommit) $
        if exclusive
          then do
            -- Commit: drop trail entries for cells >= the caller's RHB.
            loopL <- lbl' "keep"
            nextL <- lbl' "keep_next"
            doneL <- lbl' "keep_done"
            emit
              [ JLoadImm RHB RE frameHB,
                JLoadImm RT0 RE frameTR,
                JMov RT1 RT0,
                JLabel loopL,
                JBranchCmp JGe RT0 RTR doneL,
                JLoadIx RT2 RTrail RT0,
                JShr RT3 RT2 1,
                JBranchCmp JGe RT3 RHB nextL,
                JStoreIx RT2 RTrail RT1,
                JAddImm RT1 RT1 1,
                JLabel nextL,
                JAddImm RT0 RT0 1,
                JJump loopL,
                JLabel doneL,
                JMov RTR RT1
              ]
          else
            -- Link RE into the native choice-point chain for clause k + 1.
            emit
              [ JLoadLabel RT0 (retryLbl (k + 1)),
                JStoreImm RT0 RE frameNextAlt,
                JStoreImm RE RState stateBIdx,
                JMov RHB RH
              ]
      compileBody env idx unitCanReclaimH cl (lbl ++ "_c" ++ show k) True rest
    let undo
          | isLast || remNoUndoOnFail = []
          | otherwise =
              [ JLabel (undoLbl k),
                JLoadImm RT0 RE frameTR,
                JLabel (undoLbl k ++ "_loop"),
                JBranchCmp JLe RTR RT0 (undoLbl k ++ "_done"),
                JSubImm RTR RTR 1,
                JLoadIx RT1 RTrail RTR,
                JShr RT1 RT1 1,
                JMkWord RT2 RT1 tagRef,
                JStoreIx RT2 RCells RT1,
                JJump (undoLbl k ++ "_loop"),
                JLabel (undoLbl k ++ "_done"),
                JLoadImm RH RE frameH,
                JJump (clauseLbl (k + 1))
              ]
        retry
          | isLast || exclusive = []
          | otherwise =
              [ JLabel (retryLbl (k + 1)),
                JLoadImm RT0 RE frameTR,
                JLabel (retryLbl (k + 1) ++ "_loop"),
                JBranchCmp JLe RTR RT0 (retryLbl (k + 1) ++ "_done"),
                JSubImm RTR RTR 1,
                JLoadIx RT1 RTrail RTR,
                JShr RT1 RT1 1,
                JMkWord RT2 RT1 tagRef,
                JStoreIx RT2 RCells RT1,
                JJump (retryLbl (k + 1) ++ "_loop"),
                JLabel (retryLbl (k + 1) ++ "_done"),
                JLoadImm RH RE frameH,
                JLoadImm RDepth RE frameDepth,
                JAddImm RSP RE (8 * frameSize),
                JLoadImm RT0 RE framePrevB,
                JStoreImm RT0 RState stateBIdx
              ]
                ++ loadArgsOps
                ++ [JMov RHB RH | not (Set.member (k + 1) groupLastSet)]
                ++ [JJump (clauseLbl (k + 1))]
    pure (relabel (lbl ++ "_c" ++ show k ++ "_") ops ++ undo ++ retry)
  let sharedUndo
        | not isArg0Switch = []
        | otherwise =
            [ JLabel sharedUndoFailLbl,
              JLoadImm RT0 RE frameTR,
              JLabel (sharedUndoFailLbl ++ "_loop"),
              JBranchCmp JLe RTR RT0 (sharedUndoFailLbl ++ "_done"),
              JSubImm RTR RTR 1,
              JLoadIx RT1 RTrail RTR,
              JShr RT1 RT1 1,
              JMkWord RT2 RT1 tagRef,
              JStoreIx RT2 RCells RT1,
              JJump (sharedUndoFailLbl ++ "_loop"),
              JLabel (sharedUndoFailLbl ++ "_done"),
              JLoadImm RH RE frameH,
              JJump "fail"
            ]
  pure (entry ++ concat blocks ++ sharedUndo)
  where
    relabel pre = map $ \case
      JLabel l | local l -> JLabel (pre ++ l)
      JJump l | local l -> JJump (pre ++ l)
      JBranchCmp c a b l | local l -> JBranchCmp c a b (pre ++ l)
      JBranchImm c a k l | local l -> JBranchImm c a k (pre ++ l)
      JLoadLabel r l | local l -> JLoadLabel r (pre ++ l)
      JBindRef a b l | local l -> JBindRef a b (pre ++ l)
      JAddChecked d a b l | local l -> JAddChecked d a b (pre ++ l)
      JSubChecked d a b l | local l -> JSubChecked d a b (pre ++ l)
      JMulChecked d a b l | local l -> JMulChecked d a b (pre ++ l)
      JModChecked d a b l | local l -> JModChecked d a b (pre ++ l)
      JTickDepth l | local l -> JTickDepth (pre ++ l)
      JTickDepthReg r l | local l -> JTickDepthReg r (pre ++ l)
      op -> op
    local l = take 2 l == "L_"

-- | Branch to @failLbl@ unless argument @p@ is an immediate integer.
intCheck :: Int -> Label -> [JitOp]
intCheck p failLbl =
  [ JLoadImm RT0 RArgs p,
    JDeref RT0 RT0,
    JTagOf RT1 RT0,
    JBranchImm JNe RT1 (fromIntegral tagInt) failLbl
  ]

-- | Branch to @failLbl@ unless argument @p@ is ground now (a structure only
-- when its ground memo is set, which is conservative).
groundCheck :: String -> Int -> Label -> [JitOp]
groundCheck base p failLbl =
  let ok = base ++ "_ok"
   in [ JLoadImm RT0 RArgs p,
        JDeref RT0 RT0,
        JTagOf RT1 RT0,
        JBranchImm JEq RT1 (fromIntegral tagRef) failLbl,
        JBranchImm JNe RT1 (fromIntegral tagStr) ok,
        JValOf RT0 RT0,
        JLoadIx RT0 RCells RT0,
        JMovImm RT1 (fromIntegral groundBit),
        JAnd RT0 RT0 RT1,
        JBranchImm JEq RT0 0 failLbl,
        JLabel ok
      ]

-- | Branch to @failLbl@ if argument @p@ is a boxed value or a non-ground
-- structure (unbound @tagRef@, immediate constants, and ground structures pass).
argSafeCheck :: String -> Int -> Label -> [JitOp]
argSafeCheck base p failLbl =
  let ok = base ++ "_ok"
   in [ JLoadImm RT0 RArgs p,
        JDeref RT0 RT0,
        JTagOf RT1 RT0,
        JBranchImm JEq RT1 (fromIntegral tagBox) failLbl,
        JBranchImm JNe RT1 (fromIntegral tagStr) ok,
        JValOf RT0 RT0,
        JLoadIx RT0 RCells RT0,
        JMovImm RT1 (fromIntegral groundBit),
        JAnd RT0 RT0 RT1,
        JBranchImm JEq RT0 0 failLbl,
        JLabel ok
      ]

lbl' :: String -> G Label
lbl' = newLabel . ("L_" ++)

matchArg :: CEnv -> Bool -> Bool -> Set.Set (Int, [Int]) -> (Int, [Int]) -> S.Term -> Int -> Label -> Maybe Label -> G ()
matchArg env isGnd isFreshOut ro path t i failL mDirectNext = do
  r <- allocReg
  emit [JLoadImm r RArgs i]
  if isFreshOut
    then matchFreshOutArg env t r failL
    else matchTermWith env isGnd (Just ro) path t r failL mDirectNext
  freeReg r

-- | Match a head argument proven to be a freshly allocated, unaliased
-- unbound @tagRef@ cell at every call site in the unit: elides the dead
-- read-mode matcher and binds the built term directly without occurs checks.
matchFreshOutArg :: CEnv -> S.Term -> Reg -> Label -> G ()
matchFreshOutArg env t w failL = case t of
  S.Var v
    | v < 0 -> pure ()
    | otherwise -> do
        seen <- isSeen v
        sv <- slot v
        if seen
          then do
            r <- allocReg
            emit [JLoadImm r RE sv]
            unifyWords r w failL
            freeReg r
          else emit [JStoreImm w RE sv] >> markSeen v
  S.Compound _ _ -> do
    emit [JDeref w w, JTagOf RT7 w, JBranchImm JNe RT7 (fromIntegral tagRef) "rerun"]
    b <- buildTerm env t
    emit [JValOf w w, JBindRef w b "rerun"]
    freeReg b
  _ -> case constWord env t of
    Just cw ->
      emit
        [ JDeref w w,
          JTagOf RT7 w,
          JBranchImm JNe RT7 (fromIntegral tagRef) "rerun",
          JValOf w w,
          JMovImm RT7 cw,
          JBindRef w RT7 "rerun"
        ]
    Nothing -> decline ("constant outside the fragment: " ++ show t)

matchTerm :: CEnv -> Bool -> Maybe (Set.Set (Int, [Int])) -> (Int, [Int]) -> S.Term -> Reg -> Label -> G ()
matchTerm env isGnd ro path t w failL = matchTermWith env isGnd ro path t w failL Nothing

-- | Match a term against the word in @w@ (clobbered), binding unbound cells
-- (write mode) except at read-only paths, where the call goes back to the
-- interpreter. @ro@ is 'Nothing' outside a head. When @mDirectNext@ is
-- @Just nextClauseLbl@ (for the outer tag/functor check of argument 0 before
-- any trail or heap write has occurred), a mismatch jumps directly to
-- @nextClauseLbl@ instead of going through the trail-unwind block.
matchTermWith :: CEnv -> Bool -> Maybe (Set.Set (Int, [Int])) -> (Int, [Int]) -> S.Term -> Reg -> Label -> Maybe Label -> G ()
matchTermWith env isGnd ro path t w failL mDirectNext = case t of
  S.Var v
    | v < 0 -> pure ()
    | otherwise -> do
        seen <- isSeen v
        sv <- slot v
        if seen
          then do
            r <- allocReg
            emit [JLoadImm r RE sv]
            unifyWords r w failL
            freeReg r
          else emit [JStoreImm w RE sv] >> markSeen v
  S.Compound f as -> do
    let topFailL = maybe failL id mDirectNext
    readL <- lbl' "read"
    doneL <- lbl' "done"
    emit [JDeref w w, JTagOf RT7 w, JBranchImm JEq RT7 (fromIntegral tagStr) readL, JBranchImm JNe RT7 (fromIntegral tagRef) topFailL]
    before <- get
    if readOnly
      then emit [JJump "rerun"]
      else do
        occurs <- filter (`Set.member` gsSeen before) . nub <$> pure (termVarIds t)
        b <- buildTerm env t
        let isComp = \case S.Compound _ _ -> True; _ -> False
        if null occurs
          then emit [JValOf w w, JBindRef w b "rerun", JJump doneL]
          else if not (any isComp as)
            then do
              unifyWords w b failL
              emit [JJump doneL]
            else do
              occursChecks occurs w failL
              emit [JValOf w w, JBindRef w b "rerun", JJump doneL]
        freeReg b
    afterWrite <- get
    put afterWrite {gsSeen = gsSeen before, gsFree = gsFree before}
    emit [JLabel readL]
    let s = w
    tmp <- allocReg
    emit
      [ JValOf s w,
        JLoadIx RT7 RCells s,
        JMovImm tmp (complement (fromIntegral groundBit)),
        JAnd RT7 RT7 tmp,
        JMovImm tmp (funW env f (length as)),
        JBranchCmp JNe RT7 tmp topFailL
      ]
    freeReg tmp
    -- The deepest argument last, in the structure's own register, so a
    -- chain of nested structures holds one register.
    let ordered = sortOn (\(_, a) -> depth a) (zip [1 ..] as)
        depth = \case
          S.Compound _ bs -> 1 + maximum (0 : map depth bs)
          _ -> 0 :: Int
        initial = if null ordered then [] else init ordered
    forM_ initial $ \(k, a) -> do
      r <- allocReg
      emit [JAddImm r s k, JLoadIx r RCells r]
      matchTerm env isGnd ro (fst path, snd path ++ [k]) a r failL
      freeReg r
    case reverse ordered of
      (k, a) : _ -> do
        emit [JAddImm RT7 s k, JLoadIx s RCells RT7]
        matchTerm env isGnd ro (fst path, snd path ++ [k]) a s failL
      [] -> pure ()
    emit [JLabel doneL]
    -- Both modes give the same variables a slot.
    modify' (\st -> st {gsSeen = gsSeen st `Set.union` gsSeen afterWrite})
  _ -> case constWord env t of
    Just cw -> do
      let topFailL = maybe failL id mDirectNext
      okL <- lbl' "ok"
      emit [JDeref w w, JMovImm RT7 cw, JBranchCmp JEq w RT7 okL, JTagOf RT7 w, JBranchImm JNe RT7 (fromIntegral tagRef) topFailL]
      if readOnly
        then emit [JJump "rerun"]
        else emit [JValOf w w, JMovImm RT7 cw, JBindRef w RT7 "rerun"]
      emit [JLabel okL]
    Nothing -> decline ("constant outside the fragment: " ++ show t)
  where
    readOnly = isGnd || maybe False (Set.member path) ro

-- | Unify two words: identical words finish in 1 instruction; distinct words
-- store the operands in @RSP[0..1]@, failure target in @RSP[8]@, and success
-- target in @RT7@ before jumping to the shared @unify_slow@ subroutine.
unifyWords :: Reg -> Reg -> Label -> G ()
unifyWords a b failL = do
  done <- lbl' "u_done"
  emit
    [ JBranchCmp JEq a b done,
      JStoreImm a RSP 0,
      JStoreImm b RSP 1,
      JLoadLabel RT7 failL,
      JStoreImm RT7 RSP 8,
      JLoadLabel RT7 done,
      JJump "unify_slow",
      JLabel done
    ]

-- | Per-unit shared slow path for 'unifyWords': saves @RT0..RT5@ to
-- @RSP[2..7]@ and @RT7@ (done label) to @RSP[9]@, dereferences the two
-- operands from @RSP[0..1]@ into @RT0@ and @RT1@, and handles unbound cells,
-- constants, 1-level occurs checks, and 1-level structure unification.
-- Leaves @RT6@ untouched.
unifySlowOps :: [JitOp]
unifySlowOps =
  let a = RT0
      b = RT1
      r0 = RT2
      r1 = RT3
      r2 = RT4
      r3 = RT5
      unspill =
        [ JLoadImm RT0 RSP 2,
          JLoadImm RT1 RSP 3,
          JLoadImm RT2 RSP 4,
          JLoadImm RT3 RSP 5,
          JLoadImm RT4 RSP 6,
          JLoadImm RT5 RSP 7
        ]
   in [ JLabel "unify_slow",
        JStoreImm RT7 RSP 9,
        JStoreImm RT0 RSP 2,
        JStoreImm RT1 RSP 3,
        JStoreImm RT2 RSP 4,
        JStoreImm RT3 RSP 5,
        JStoreImm RT4 RSP 6,
        JStoreImm RT5 RSP 7,
        JLoadImm a RSP 0,
        JLoadImm b RSP 1,
        JDeref a a,
        JDeref b b,
        JBranchCmp JEq a b "us_done",
        JTagOf RT7 a,
        JBranchImm JEq RT7 (fromIntegral tagRef) "us_aref",
        JTagOf RT7 b,
        JBranchImm JEq RT7 (fromIntegral tagRef) "us_bref",
        JTagOf RT7 a,
        JBranchImm JEq RT7 (fromIntegral tagStr) "us_astr",
        JBranchImm JEq RT7 (fromIntegral tagBox) "rerun",
        JJump "us_fail",
        JLabel "us_aref",
        JTagOf RT7 b,
        JBranchImm JEq RT7 (fromIntegral tagRef) "us_both",
        JBranchImm JEq RT7 (fromIntegral tagStr) "us_aref_bstr",
        JValOf a a,
        JBindRef a b "rerun",
        JJump "us_done",
        JLabel "us_bref",
        JTagOf RT7 a,
        JBranchImm JEq RT7 (fromIntegral tagStr) "us_bref_astr",
        JValOf b b,
        JBindRef b a "rerun",
        JJump "us_done",
        JLabel "us_both",
        JBranchCmp JLt a b "us_bindb",
        JValOf a a,
        JBindRef a b "rerun",
        JJump "us_done",
        JLabel "us_bindb",
        JValOf b b,
        JBindRef b a "rerun",
        JJump "us_done",
        JLabel "us_bref_astr",
        JMov RT7 a,
        JMov a b,
        JMov b RT7,
        JLabel "us_aref_bstr",
        JValOf r0 b,
        JLoadIx r1 RCells r0,
        JMovImm RT7 (fromIntegral groundBit),
        JAnd RT7 r1 RT7,
        JBranchImm JNe RT7 0 "us_bind_ref_str_ok",
        JValOf r1 r1,
        JMovImm RT7 0x7FFFF,
        JAnd r1 r1 RT7,
        JLabel "us_occ_loop",
        JBranchImm JEq r1 0 "us_bind_ref_str_ok",
        JAddImm r0 r0 1,
        JLoadIx r2 RCells r0,
        JDeref r2 r2,
        JBranchCmp JEq r2 a "us_fail",
        JTagOf RT7 r2,
        JBranchImm JNe RT7 (fromIntegral tagStr) "us_occ_next",
        JValOf r3 r2,
        JLoadIx r2 RCells r3,
        JMovImm RT7 (fromIntegral groundBit),
        JAnd RT7 r2 RT7,
        JBranchImm JNe RT7 0 "us_occ_next",
        JBranchImm JNe r1 1 "us_occ_child",
        JMov r0 r3,
        JValOf r1 r2,
        JMovImm RT7 0x7FFFF,
        JAnd r1 r1 RT7,
        JJump "us_occ_loop",
        JLabel "us_occ_child",
        JValOf r2 r2,
        JMovImm RT7 0x7FFFF,
        JAnd r2 r2 RT7,
        JLabel "us_occ_cloop",
        JBranchImm JEq r2 0 "us_occ_next",
        JAddImm r3 r3 1,
        JLoadIx RT7 RCells r3,
        JDeref RT7 RT7,
        JBranchCmp JEq RT7 a "us_fail",
        JTagOf RT7 RT7,
        JBranchImm JEq RT7 (fromIntegral tagStr) "rerun",
        JSubImm r2 r2 1,
        JJump "us_occ_cloop",
        JLabel "us_occ_next",
        JSubImm r1 r1 1,
        JJump "us_occ_loop",
        JLabel "us_bind_ref_str_ok",
        JValOf a a,
        JBindRef a b "rerun",
        JJump "us_done",
        JLabel "us_astr",
        JTagOf RT7 b,
        JBranchImm JNe RT7 (fromIntegral tagStr) "us_fail",
        JValOf a a,
        JValOf b b,
        JLoadIx r0 RCells a,
        JLoadIx r1 RCells b,
        JMovImm RT7 (complement (fromIntegral groundBit)),
        JAnd r0 r0 RT7,
        JAnd r1 r1 RT7,
        JBranchCmp JNe r0 r1 "us_fail",
        JValOf r0 r0,
        JMovImm RT7 0x7FFFF,
        JAnd r0 r0 RT7,
        JLabel "us_str_loop",
        JBranchImm JEq r0 0 "us_done",
        JAddImm a a 1,
        JAddImm b b 1,
        JLoadIx r1 RCells a,
        JDeref r1 r1,
        JLoadIx r2 RCells b,
        JDeref r2 r2,
        JBranchCmp JEq r1 r2 "us_str_next",
        JTagOf r3 r1,
        JTagOf RT7 r2,
        JBranchImm JEq r3 (fromIntegral tagRef) "us_str_aref",
        JBranchImm JEq RT7 (fromIntegral tagRef) "us_str_bref",
        JBranchCmp JNe r3 RT7 "us_fail",
        JBranchImm JEq r3 (fromIntegral tagStr) "rerun",
        JBranchImm JEq r3 (fromIntegral tagBox) "rerun",
        JJump "us_fail",
        JLabel "us_str_aref",
        JBranchImm JNe RT7 (fromIntegral tagRef) "us_str_anonref",
        JBranchCmp JLt r1 r2 "us_str_bindb",
        JValOf r1 r1,
        JBindRef r1 r2 "rerun",
        JJump "us_str_next",
        JLabel "us_str_bindb",
        JValOf r2 r2,
        JBindRef r2 r1 "rerun",
        JJump "us_str_next",
        JLabel "us_str_anonref",
        JBranchImm JNe RT7 (fromIntegral tagStr) "us_str_abind",
        JValOf r3 r2,
        JLoadIx r3 RCells r3,
        JMovImm RT7 (fromIntegral groundBit),
        JAnd r3 r3 RT7,
        JBranchImm JEq r3 0 "rerun",
        JLabel "us_str_abind",
        JValOf r1 r1,
        JBindRef r1 r2 "rerun",
        JJump "us_str_next",
        JLabel "us_str_bref",
        JBranchImm JNe r3 (fromIntegral tagStr) "us_str_bbind",
        JValOf r3 r1,
        JLoadIx r3 RCells r3,
        JMovImm RT7 (fromIntegral groundBit),
        JAnd r3 r3 RT7,
        JBranchImm JEq r3 0 "rerun",
        JLabel "us_str_bbind",
        JValOf r2 r2,
        JBindRef r2 r1 "rerun",
        JLabel "us_str_next",
        JSubImm r0 r0 1,
        JJump "us_str_loop",
        JLabel "us_fail"
      ]
        ++ unspill
        ++ [ JLoadImm RT7 RSP 8,
             JJumpReg RT7,
             JLabel "us_done"
           ]
        ++ unspill
        ++ [ JLoadImm RT7 RSP 9,
             JJumpReg RT7
           ]

-- | Before binding the unbound cell in @w@ to a new structure holding the
-- values of earlier variables: a variable that is the cell itself fails
-- (occurs check); one holding a structure not marked ground goes to the
-- interpreter, which walks it.
occursChecks :: [S.VarId] -> Reg -> Label -> G ()
occursChecks vs w failL = forM_ vs $ \v -> do
  t <- allocReg
  sv <- slot v
  okL <- lbl' "occ"
  emit
    [ JLoadImm t RE sv,
      JDeref t t,
      JBranchCmp JEq t w failL,
      JTagOf RT7 t,
      JBranchImm JNe RT7 (fromIntegral tagStr) okL,
      JValOf t t,
      JLoadIx t RCells t,
      JMovImm RT7 (fromIntegral groundBit),
      JAnd t t RT7,
      JBranchImm JEq t 0 "rerun",
      JLabel okL
    ]
  freeReg t

-- | Cells a term needs on the heap.
termCells :: Set.Set S.VarId -> S.Term -> Int
termCells seen = \case
  S.Var v | v < 0 || not (Set.member v seen) -> 1
  S.Compound _ as -> 1 + length as + sum [termCells seen a | a@(S.Compound _ _) <- as]
  _ -> 0

-- | Build a term on the heap; the register returned holds its word. Fresh
-- variables are unbound cells (inside a structure, the argument cell).
buildTerm :: CEnv -> S.Term -> G Reg
buildTerm env t = do
  seen <- gets gsSeen
  let cells = termCells seen t
  when (cells > 0) $ do
    r <- allocReg
    c <- allocReg
    emit [JAddImm r RH cells, JLoadImm c RState stateCapIdx, JBranchCmp JGt r c "bailout"]
    freeReg c
    freeReg r
  build t
  where
    build = \case
      S.Var v
        | v >= 0 -> do
            seen <- isSeen v
            sv <- slot v
            r <- allocReg
            if seen
              then emit [JLoadImm r RE sv, JDeref r r]
              else do
                emit [JMkWord r RH tagRef, JStoreIx r RCells RH, JAddImm RH RH 1, JStoreImm r RE sv]
                markSeen v
            pure r
        | otherwise -> do
            r <- allocReg
            emit [JMkWord r RH tagRef, JStoreIx r RCells RH, JAddImm RH RH 1]
            pure r
      S.Compound f as -> do
        (b, _) <- buildStruct f as
        pure b
      c -> case constWord env c of
        Just cw -> do
          r <- allocReg
          emit [JMovImm r cw]
          pure r
        Nothing -> decline ("constant outside the fragment: " ++ show c)
    -- Reserve the structure's cells at RH, then fill each argument in order
    -- using RH-relative offsets so that zero registers are held live across
    -- recursive buildStruct calls (allowing arbitrary structure nesting depth).
    structCells = \case
      S.Compound _ bs -> 1 + length bs + sum (map structCells bs)
      _ -> 0
    buildStruct f as = do
      let n = length as
          fw = funW env f n
      seen0 <- gets gsSeen
      let hasFresh term = any (\v -> v < 0 || not (Set.member v seen0)) (allVarsIn term)
          staticNon = any hasFresh as
          seenVarCount = length [() | S.Var v <- as, v >= 0, Set.member v seen0]
          isComp = \case S.Compound _ _ -> True; _ -> False
          batchGroundCheck = not staticNon && not (any isComp as) && seenVarCount >= 2
      emit [JMovImm RT7 (if staticNon then fw else fw .|. fromIntegral groundBit), JStoreIx RT7 RCells RH, JAddImm RH RH (n + 1)]
      let store off k r = do
            a' <- allocReg
            emit [JSubImm a' RH (off - k), JStoreIx r RCells a']
            freeReg a'
          freshCell off k = do
            a' <- allocReg
            emit [JSubImm a' RH (off - k), JMkWord RT7 a' tagRef, JStoreIx RT7 RCells a']
            freeReg a'
          fill !off _ [] = pure off
          fill !off !k (a : rest) = case a of
            S.Var v
              | v < 0 -> freshCell off k >> fill off (k + 1) rest
              | otherwise -> do
                  seen <- isSeen v
                  sv <- slot v
                  if not seen
                    then do
                      freshCell off k
                      emit [JStoreImm RT7 RE sv]
                      markSeen v
                    else do
                      w <- allocReg
                      emit [JLoadImm w RE sv]
                      store off k w
                      unless (staticNon || batchGroundCheck) (groundOrClear w off fw)
                      freeReg w
                  fill off (k + 1) rest
            S.Compound g bs -> do
              (cb, childStatic) <- buildStruct g bs
              let !off' = off + structCells a
              store off' k cb
              unless staticNon $ case childStatic of
                Just True -> pure ()
                Just False -> do
                  a' <- allocReg
                  emit [JSubImm a' RH off', JMovImm RT7 fw, JStoreIx RT7 RCells a']
                  freeReg a'
                Nothing -> groundOrClear cb off' fw
              freeReg cb
              fill off' (k + 1) rest
            c -> case constWord env c of
              Just cw -> do
                a' <- allocReg
                emit [JSubImm a' RH (off - k), JMovImm RT7 cw, JStoreIx RT7 RCells a']
                freeReg a'
                fill off (k + 1) rest
              Nothing -> decline ("constant outside the fragment: " ++ show c)
      totalOff <- fill (n + 1) (1 :: Int) as
      b <- allocReg
      emit [JSubImm b RH totalOff]
      when batchGroundCheck $ do
        retL <- lbl' "gnds"
        emit
          [ JStoreImm b RSP 1,
            JMovImm RT7 fw,
            JStoreImm RT7 RSP 2,
            JMovImm RT7 (fromIntegral n),
            JStoreImm RT7 RSP 0,
            JLoadLabel RT7 retL,
            JJump "gnd_struct",
            JLabel retL
          ]
      emit [JMkWord b b tagStr]
      let static
            | staticNon = Just False
            | all constant as = Just True
            | otherwise = Nothing
      pure (b, static)
    constant = \case
      S.Var _ -> False
      S.Compound _ bs -> all constant bs
      _ -> True
    groundOrClear w off fw = do
      retL <- lbl' "gnd"
      emit
        [ JStoreImm w RSP 0,
          JSubImm RT7 RH off,
          JStoreImm RT7 RSP 1,
          JMovImm RT7 fw,
          JStoreImm RT7 RSP 2,
          JLoadLabel RT7 retL,
          JJump "gnd_clear",
          JLabel retL
        ]

-- | Per-unit shared helpers for 'groundOrClear' and 'gnd_struct':
-- * @gnd_clear@ tests whether the word in @RSP[0]@ is ground, and if not,
--   clears the structure header at @RSP[1]@ using @RSP[2]@.
-- * @gnd_struct@ loops over @RSP[0]@ fields of the flat structure at cell
--   @RSP[1]@, clearing its header to @RSP[2]@ if any field is non-ground.
-- Both return to @RT7@.
gndClearOps :: [JitOp]
gndClearOps =
  [ JLabel "gnd_clear",
    JStoreImm RT0 RSP 3,
    JStoreImm RT1 RSP 4,
    JLoadImm RT0 RSP 0,
    JDeref RT0 RT0,
    JTagOf RT1 RT0,
    JBranchImm JEq RT1 (fromIntegral tagRef) "gc_clear",
    JBranchImm JNe RT1 (fromIntegral tagStr) "gc_ret",
    JValOf RT0 RT0,
    JLoadIx RT0 RCells RT0,
    JMovImm RT1 (fromIntegral groundBit),
    JAnd RT0 RT0 RT1,
    JBranchImm JNe RT0 0 "gc_ret",
    JLabel "gc_clear",
    JLoadImm RT0 RSP 1,
    JLoadImm RT1 RSP 2,
    JStoreIx RT1 RCells RT0,
    JLabel "gc_ret",
    JLoadImm RT0 RSP 3,
    JLoadImm RT1 RSP 4,
    JJumpReg RT7,
    JLabel "gnd_struct",
    JStoreImm RT0 RSP 3,
    JStoreImm RT1 RSP 4,
    JStoreImm RT2 RSP 5,
    JStoreImm RT3 RSP 6,
    JLoadImm RT2 RSP 0,
    JLoadImm RT3 RSP 1,
    JLabel "gs_loop",
    JBranchImm JEq RT2 0 "gs_ret",
    JAddImm RT3 RT3 1,
    JLoadIx RT0 RCells RT3,
    JDeref RT0 RT0,
    JTagOf RT1 RT0,
    JBranchImm JEq RT1 (fromIntegral tagRef) "gs_clear",
    JBranchImm JNe RT1 (fromIntegral tagStr) "gs_next",
    JValOf RT0 RT0,
    JLoadIx RT0 RCells RT0,
    JMovImm RT1 (fromIntegral groundBit),
    JAnd RT0 RT0 RT1,
    JBranchImm JEq RT0 0 "gs_clear",
    JLabel "gs_next",
    JSubImm RT2 RT2 1,
    JJump "gs_loop",
    JLabel "gs_clear",
    JLoadImm RT0 RSP 1,
    JLoadImm RT1 RSP 2,
    JStoreIx RT1 RCells RT0,
    JLabel "gs_ret",
    JLoadImm RT0 RSP 3,
    JLoadImm RT1 RSP 4,
    JLoadImm RT2 RSP 5,
    JLoadImm RT3 RSP 6,
    JJumpReg RT7
  ]

-- | An integer expression into a register, untagged. A value that is not an
-- immediate integer, or a result outside one, goes to the interpreter.
evalExpr :: S.Term -> G Reg
evalExpr = \case
  S.IntLit k -> do
    r <- allocReg
    emit [JMovImm r (fromIntegral k)]
    pure r
  S.Var v | v >= 0 -> do
    seen <- isSeen v
    unless seen (decline "arithmetic on an unbound variable")
    sv <- slot v
    r <- allocReg
    emit [JLoadImm r RE sv, JDeref r r, JTagOf RT7 r, JBranchImm JNe RT7 (fromIntegral tagInt) "rerun", JValOf r r]
    pure r
  S.Compound op [a, b] | op `elem` ["plus", "minus", "mul", "mod"] -> do
    ra <- evalExpr a
    rb <- evalExpr b
    emit
      [ case op of
          "plus" -> JAddChecked ra ra rb "rerun"
          "minus" -> JSubChecked ra ra rb "rerun"
          "mul" -> JMulChecked ra ra rb "rerun"
          _ -> JModChecked ra ra rb "rerun"
      ]
    freeReg rb
    pure ra
  e -> decline ("expression outside the fragment: " ++ show e)

-- | Match a dereferenced register against a ground term without binding.
matchGroundTerm :: CEnv -> S.Term -> Reg -> Label -> G ()
matchGroundTerm env t w failL = case t of
  S.Compound f as -> do
    emit [JDeref w w, JTagOf RT7 w, JBranchImm JNe RT7 (fromIntegral tagStr) failL]
    let s = w
    tmp <- allocReg
    emit
      [ JValOf s w,
        JLoadIx RT7 RCells s,
        JMovImm tmp (complement (fromIntegral groundBit)),
        JAnd RT7 RT7 tmp,
        JMovImm tmp (funW env f (length as)),
        JBranchCmp JNe RT7 tmp failL
      ]
    freeReg tmp
    let ordered = sortOn (\(_, a) -> depth a) (zip [1 ..] as)
        depth = \case
          S.Compound _ bs -> 1 + maximum (0 : map depth bs)
          _ -> 0 :: Int
        initial = if null ordered then [] else init ordered
    forM_ initial $ \(k, a) -> do
      r <- allocReg
      emit [JAddImm r s k, JLoadIx r RCells r]
      matchGroundTerm env a r failL
      freeReg r
    case reverse ordered of
      (k, a) : _ -> do
        emit [JAddImm RT7 s k, JLoadIx s RCells RT7]
        matchGroundTerm env a s failL
      [] -> pure ()
  _ -> case constWord env t of
    Just cw -> emit [JDeref w w, JMovImm RT7 cw, JBranchCmp JNe w RT7 failL]
    Nothing -> decline ("constant outside the fragment: " ++ show t)

-- | Structural equality (@==@) or disequality (@!=@) between two operands,
-- branching to @eqL@ when equal and @neL@ when distinct; reruns on the
-- interpreter when @requireGround@ is True and either operand is non-ground,
-- or when both operands are boxed values or structures with the same functor
-- at different cells.
compileEquivBranch :: CEnv -> Bool -> S.Term -> S.Term -> Label -> Label -> G ()
compileEquivBranch env requireGround a b eqL neL = do
  ra <- loadOperand a
  rb <- loadOperand b
  t1 <- allocReg
  t2 <- allocReg
  when requireGround $ do
    gndA <- lbl' "eq_ga"
    gndB <- lbl' "eq_gb"
    emit
      [ JTagOf t1 ra,
        JBranchImm JEq t1 (fromIntegral tagRef) "rerun",
        JBranchImm JNe t1 (fromIntegral tagStr) gndA,
        JValOf t2 ra,
        JLoadIx t2 RCells t2,
        JMovImm RT7 (fromIntegral groundBit),
        JAnd t2 t2 RT7,
        JBranchImm JEq t2 0 "rerun",
        JLabel gndA,
        JTagOf t2 rb,
        JBranchImm JEq t2 (fromIntegral tagRef) "rerun",
        JBranchImm JNe t2 (fromIntegral tagStr) gndB,
        JValOf t1 rb,
        JLoadIx t1 RCells t1,
        JMovImm RT7 (fromIntegral groundBit),
        JAnd t1 t1 RT7,
        JBranchImm JEq t1 0 "rerun",
        JLabel gndB
      ]
  emit
    [ JBranchCmp JEq ra rb eqL,
      JTagOf t1 ra,
      JTagOf t2 rb,
      JBranchCmp JNe t1 t2 neL,
      JBranchImm JEq t1 (fromIntegral tagBox) "rerun",
      JBranchImm JNe t1 (fromIntegral tagStr) neL,
      JValOf ra ra,
      JValOf rb rb,
      JLoadIx ra RCells ra,
      JLoadIx rb RCells rb,
      JMovImm RT7 (complement (fromIntegral groundBit)),
      JAnd ra ra RT7,
      JAnd rb rb RT7,
      JBranchCmp JNe ra rb neL,
      JJump "rerun"
    ]
  freeReg t2
  freeReg t1
  freeReg rb
  freeReg ra
  where
    loadOperand term = do
      r <- allocReg
      case term of
        S.Var v
          | v >= 0 -> do
              seen <- isSeen v
              sv <- slot v
              if seen
                then emit [JLoadImm r RE sv, JDeref r r]
                else do
                  c <- allocReg
                  emit
                    [ JAddImm c RH 1,
                      JLoadImm RT7 RState stateCapIdx,
                      JBranchCmp JGt c RT7 "bailout",
                      JMkWord r RH tagRef,
                      JStoreIx r RCells RH,
                      JAddImm RH RH 1,
                      JStoreImm r RE sv
                    ]
                  freeReg c
                  markSeen v
          | otherwise -> do
              c <- allocReg
              emit
                [ JAddImm c RH 1,
                  JLoadImm RT7 RState stateCapIdx,
                  JBranchCmp JGt c RT7 "bailout",
                  JMkWord r RH tagRef,
                  JStoreIx r RCells RH,
                  JAddImm RH RH 1
                ]
              freeReg c
        _ -> case constWord env term of
          Just cw -> emit [JMovImm r cw]
          Nothing -> decline ("operand outside the fragment: " ++ show term)
      pure r

compileGuard :: CEnv -> Label -> S.Term -> G ()
compileGuard env failL = \case
  S.Atom "true" -> pure ()
  S.Atom "fail" -> emit [JJump failL]
  S.Atom "false" -> emit [JJump failL]
  S.Compound "is" [lhs, e] -> do
    r <- evalExpr e
    case lhs of
      S.IntLit k -> emit [JBranchImm JNe r (fromIntegral k) failL]
      S.Var v | v >= 0 -> do
        seen <- isSeen v
        sv <- slot v
        emit [JMkWord r r tagInt]
        if not seen
          then emit [JStoreImm r RE sv] >> markSeen v
          else do
            t <- allocReg
            okL <- lbl' "is"
            emit
              [ JLoadImm t RE sv,
                JDeref t t,
                JBranchCmp JEq t r okL,
                JTagOf RT7 t,
                JBranchImm JNe RT7 (fromIntegral tagRef) failL,
                JValOf t t,
                JBindRef t r "rerun",
                JLabel okL
              ]
            freeReg t
      _ -> decline "is with a target outside the fragment"
    freeReg r
  S.Compound op [a, b] | Just cond <- negated op -> do
    ra <- evalExpr a
    rb <- evalExpr b
    emit [JBranchCmp cond ra rb failL]
    freeReg rb
    freeReg ra
  -- Structural disequality: decided when both sides are ground.
  S.Compound "neq" [a, b] -> do
    okL <- lbl' "neq_ok"
    compileEquivBranch env True a b failL okL
    emit [JLabel okL]
  S.Compound "equiv" [a, b]
    | atomicOk a && atomicOk b -> do
        okL <- lbl' "eq_ok"
        compileEquivBranch env False a b okL failL
        emit [JLabel okL]
    | S.Var v <- a, v >= 0, groundTermOk b -> do
        seen <- isSeen v
        if not seen
          then emit [JJump failL]
          else do
            sv <- slot v
            r <- allocReg
            emit [JLoadImm r RE sv]
            matchGroundTerm env b r failL
            freeReg r
    | groundTermOk a, S.Var v <- b, v >= 0 -> do
        seen <- isSeen v
        if not seen
          then emit [JJump failL]
          else do
            sv <- slot v
            r <- allocReg
            emit [JLoadImm r RE sv]
            matchGroundTerm env a r failL
            freeReg r
  S.Compound "is_int" [x] -> compileTypeTest x (Just tagInt) True False failL
  S.Compound "is_atom" [x] -> compileTypeTest x (Just tagAtm) False False failL
  S.Compound "is_char" [x] -> compileTypeTest x (Just tagChr) False False failL
  S.Compound "var" [x] -> compileVarTest x True failL
  S.Compound "nonvar" [x] -> compileVarTest x False failL
  S.Compound "ground" [x] -> compileGroundTest x failL
  S.Compound "not" [g] -> case flatten g of
    [single] -> compileNegatedTest env failL single
    _ -> decline ("guard outside the fragment: " ++ show g)
  g -> decline ("guard outside the fragment: " ++ show g)
  where
    negated = \case
      "lt" -> Just JGe
      "lte" -> Just JGt
      "gt" -> Just JLe
      "gte" -> Just JLt
      _ -> Nothing

compileNegatedTest :: CEnv -> Label -> S.Term -> G ()
compileNegatedTest env failL = \case
  S.Compound "equiv" [a, b] | atomicOk a && atomicOk b -> do
    okL <- lbl' "neq_ok"
    compileEquivBranch env False a b failL okL
    emit [JLabel okL]
  S.Compound "neq" [a, b] | atomicOk a && atomicOk b -> do
    okL <- lbl' "not_neq_ok"
    compileEquivBranch env True a b okL failL
    emit [JLabel okL]
  g -> do
    okL <- lbl' "not_ok"
    compileGuard env okL g
    emit [JJump failL, JLabel okL]

compileTypeTest :: S.Term -> Maybe Int -> Bool -> Bool -> Label -> G ()
compileTypeTest x mTag boxRerun invert failL = case x of
  S.Var v
    | v < 0 -> unless invert (emit [JJump failL])
    | otherwise -> do
        seen <- isSeen v
        if not seen
          then unless invert (emit [JJump failL])
          else do
            sv <- slot v
            r <- allocReg
            okL <- lbl' "type_ok"
            let matchTag = maybe (-1) fromIntegral mTag
            emit $
              [ JLoadImm r RE sv,
                JDeref r r,
                JTagOf RT7 r
              ]
                ++ [JBranchImm JEq RT7 (fromIntegral tagBox) "rerun" | boxRerun]
                ++ ( if invert
                       then [JBranchImm JEq RT7 matchTag failL]
                       else [JBranchImm JNe RT7 matchTag failL]
                   )
                ++ [JLabel okL]
            freeReg r
  S.IntLit _ -> when ((mTag == Just tagInt) == invert) (emit [JJump failL])
  S.Atom _ -> when ((mTag == Just tagAtm) == invert) (emit [JJump failL])
  S.CharLit _ -> when ((mTag == Just tagChr) == invert) (emit [JJump failL])
  _ -> unless invert (emit [JJump failL])

compileVarTest :: S.Term -> Bool -> Label -> G ()
compileVarTest x wantVar failL = case x of
  S.Var v
    | v < 0 -> unless wantVar (emit [JJump failL])
    | otherwise -> do
        seen <- isSeen v
        if not seen
          then unless wantVar (emit [JJump failL])
          else do
            sv <- slot v
            r <- allocReg
            emit
              [ JLoadImm r RE sv,
                JDeref r r,
                JTagOf RT7 r,
                JBranchImm (if wantVar then JNe else JEq) RT7 (fromIntegral tagRef) failL
              ]
            freeReg r
  _ -> when wantVar (emit [JJump failL])

compileGroundTest :: S.Term -> Label -> G ()
compileGroundTest x failL = case x of
  S.Var v
    | v < 0 -> emit [JJump failL]
    | otherwise -> do
        seen <- isSeen v
        if not seen
          then emit [JJump failL]
          else do
            sv <- slot v
            r <- allocReg
            okL <- lbl' "gnd_ok"
            emit
              [ JLoadImm r RE sv,
                JDeref r r,
                JTagOf RT7 r,
                JBranchImm JEq RT7 (fromIntegral tagRef) failL,
                JBranchImm JNe RT7 (fromIntegral tagStr) okL,
                JValOf r r,
                JLoadIx r RCells r,
                JMovImm RT7 (fromIntegral groundBit),
                JAnd r r RT7,
                JBranchImm JEq r 0 "rerun",
                JLabel okL
              ]
            freeReg r
  S.Compound _ as -> mapM_ (`compileGroundTest` failL) as
  _ -> pure ()

-- | Compile a sequence of clause body goals. When @allowTail@ is True, the
-- final goal of the sequence returns or tail-calls directly; when False
-- (inside @once@ or @not@), execution falls through so the enclosing control
-- construct can clean up.
compileBody :: CEnv -> M.Map PredKey Int -> Bool -> S.Clause -> String -> Bool -> [S.Term] -> G ()
compileBody env idx unitCanReclaimH cl base allowTail = go
  where
    headVarSet = Set.fromList (termVarIds (S.clauseHead cl))
    allClauseVars = allVarsIn (S.clauseHead cl) ++ concatMap allVarsIn (concatMap flatten (S.clauseBody cl))
    varOccurrences v = length (filter (== v) allClauseVars)
    go [] = when allowTail $ do
      skipL <- lbl' "keep_sp"
      emit $
        [ JLoadImm RT7 RE frameRet,
          JLoadImm RT0 RState stateBIdx,
          JBranchCmp JLe RE RT0 skipL,
          JMov RSP RE
        ]
          ++ [JLoadImm RH RE frameH | unitCanReclaimH]
          ++ [ JLabel skipL,
               JLoadImm RE RE frameLink,
               JJumpReg RT7
             ]
    go (g : gs) = case g of
      S.Atom "!" -> emitCut >> go gs
      S.Compound "$cut" [S.IntLit _] -> emitCut >> go gs
      S.Compound "unify" [a, b] -> unifyGoal a b >> go gs
      S.Compound "once" [inner] -> do
        let innerGoals = flatten inner
            innerVars = nub [v | x <- innerGoals, v <- termVarIds x]
            -- When no variable in inner occurs anywhere outside this once in
            -- the clause, no binding or heap cell allocated inside inner can
            -- escape once inner succeeds.
            innerVarCount v = length [u | x <- innerGoals, u <- allVarsIn x, u == v]
            deadHeap = all (\v -> varOccurrences v == innerVarCount v) innerVars
        tBase <- allocTempBlock
        let slotB = tBase
            slotHB = tBase + 1
            slotSP = tBase + 2
            slotTR = tBase + 3
            slotH = tBase + 4
        emit
          [ JLoadImm RT0 RState stateBIdx,
            JStoreImm RT0 RE slotB,
            JStoreImm RHB RE slotHB,
            JStoreImm RSP RE slotSP,
            JStoreImm RTR RE slotTR,
            JStoreImm RH RE slotH
          ]
        seenBefore <- gets gsSeen
        compileBody env idx unitCanReclaimH cl (base ++ "_once") False innerGoals
        when deadHeap $ modify' (\st -> st {gsSeen = seenBefore})
        emit
          ( [ JLoadImm RT0 RE slotB,
              JStoreImm RT0 RState stateBIdx,
              JLoadImm RHB RE slotHB,
              JLoadImm RSP RE slotSP
            ]
              ++ (if deadHeap then [JLoadImm RTR RE slotTR, JLoadImm RH RE slotH] else [])
          )
        go gs
      S.Compound "not" [inner] -> case flatten inner of
        [single] | isSimpleNegatable single -> compileNegatedTest env "fail" single >> go gs
        innerGoals -> do
          tBase <- allocTempBlock
          let slotB = tBase
          notPassL <- lbl' "not_pass"
          notFailLoopL <- lbl' "not_floop"
          notFailDoneL <- lbl' "not_fdone"
          notPassLoopL <- lbl' "not_ploop"
          notPassDoneL <- lbl' "not_pdone"
          emit
            [ JAddImm RT6 RSP (8 * (frameHeader + 10)),
              JLoadImm RT5 RState stateNStackLimIdx,
              JBranchCmp JGt RT6 RT5 "stackfull",
              JStoreImm RSP RE slotB,
              JStoreImm RE RSP frameLink,
              JStoreImm RTR RSP frameTR,
              JStoreImm RH RSP frameH,
              JLoadImm RT0 RState stateBIdx,
              JStoreImm RT0 RSP framePrevB,
              JStoreImm RHB RSP frameHB,
              JLoadLabel RT0 notPassL,
              JStoreImm RT0 RSP frameNextAlt,
              JStoreImm RDepth RSP frameDepth,
              JStoreImm RSP RState stateBIdx,
              JAddImm RSP RSP (8 * frameHeader),
              JMov RHB RH
            ]
          seenBefore <- gets gsSeen
          compileBody env idx unitCanReclaimH cl (base ++ "_not") False innerGoals
          modify' (\st -> st {gsSeen = seenBefore})
          -- Inner succeeded -> unwind to B_not and fail!
          emit
            [ JLoadImm RT3 RE slotB,
              JLoadImm RT0 RT3 frameTR,
              JLabel notFailLoopL,
              JBranchCmp JLe RTR RT0 notFailDoneL,
              JSubImm RTR RTR 1,
              JLoadIx RT1 RTrail RTR,
              JShr RT1 RT1 1,
              JMkWord RT2 RT1 tagRef,
              JStoreIx RT2 RCells RT1,
              JJump notFailLoopL,
              JLabel notFailDoneL,
              JLoadImm RH RT3 frameH,
              JLoadImm RDepth RT3 frameDepth,
              JLoadImm RT0 RT3 framePrevB,
              JStoreImm RT0 RState stateBIdx,
              JLoadImm RHB RT3 frameHB,
              JMov RSP RT3,
              JJump "fail",
              -- Inner failed -> "fail" set RE = B_not and jumped here!
              JLabel notPassL,
              JLoadImm RT0 RE frameTR,
              JLabel notPassLoopL,
              JBranchCmp JLe RTR RT0 notPassDoneL,
              JSubImm RTR RTR 1,
              JLoadIx RT1 RTrail RTR,
              JShr RT1 RT1 1,
              JMkWord RT2 RT1 tagRef,
              JStoreIx RT2 RCells RT1,
              JJump notPassLoopL,
              JLabel notPassDoneL,
              JLoadImm RH RE frameH,
              JLoadImm RDepth RE frameDepth,
              JLoadImm RT0 RE framePrevB,
              JStoreImm RT0 RState stateBIdx,
              JLoadImm RHB RE frameHB,
              JMov RSP RE,
              JLoadImm RE RE frameLink
            ]
          go gs
      _
        | isInlineGuard g -> compileGuard env "fail" g >> go gs
        | otherwise -> do
            let k = (calleeName g, length (callArgs g))
                isTailCall = null gs && allowTail
            target <- maybe (decline ("call outside the unit: " ++ show k)) pure (M.lookup k idx)
            seenBeforeCall <- gets gsSeen
            forM_ (zip [0 ..] (callArgs g)) $ \(i, a) -> do
              r <- buildTerm env a
              emit [JStoreImm r RArgs i]
              freeReg r
            if isTailCall
              then do
                skipL <- lbl' "keep_tail_sp"
                let localArgIndices =
                      [ i
                        | (i, S.Var v) <- zip [0 :: Int ..] (callArgs g),
                          v < 0 || Set.notMember v headVarSet
                      ]
                    anyFreshInTail =
                      any
                        (\a -> case a of S.Var v -> v < 0 || Set.notMember v seenBeforeCall; _ -> False)
                        (callArgs g)
                emit $
                  [ JLoadImm RT7 RE frameRet,
                    JLoadImm RT0 RState stateBIdx,
                    JBranchCmp JLe RE RT0 skipL,
                    JMov RSP RE
                  ]
                    ++ ( if unitCanReclaimH && not anyFreshInTail
                           then
                             concat
                               [ [ JLoadImm RT0 RArgs i,
                                   JTagOf RT1 RT0,
                                   JBranchImm JEq RT1 (fromIntegral tagRef) skipL
                                 ]
                                 | i <- localArgIndices
                               ]
                               ++ [JLoadImm RH RE frameH]
                           else []
                       )
                    ++ [ JLabel skipL,
                         JLoadImm RE RE frameLink,
                         JJump (predLabel target)
                       ]
              else do
                ret <- newLabel (base ++ "_ret")
                emit
                  [ JLoadLabel RT7 ret,
                    JTickDepth "exhausted",
                    JJump (predLabel target),
                    JLabel ret,
                    JMovImm RT0 (-1),
                    JTickDepthReg RT0 "exhausted"
                  ]
                go gs
    emitCut = do
      fs <- gets gsFrameSize
      emit
        [ JLoadImm RT0 RE framePrevB,
          JStoreImm RT0 RState stateBIdx,
          JLoadImm RHB RE frameHB,
          JAddImm RSP RE (8 * fs)
        ]
    calleeName = \case
      S.Atom f -> f
      S.Compound f _ -> f
      _ -> ""
    unifyGoal a b = case (a, b) of
      (S.Var v, _) | v < 0 -> pure ()
      (_, S.Var v) | v < 0 -> pure ()
      (S.Var u, S.Var v) | u == v -> pure ()
      (S.Var v, t) | v >= 0 -> withVar v t
      (t, S.Var v) | v >= 0 -> withVar v t
      _ -> decline "unification of two non-variables"
    withVar v t = do
      seen <- isSeen v
      sv <- slot v
      if not seen
        then do
          when (v `elem` termVarIds t) (decline "cyclic unification")
          r <- buildTerm env t
          emit [JStoreImm r RE sv]
          markSeen v
          freeReg r
        else do
          r <- allocReg
          emit [JLoadImm r RE sv]
          matchTerm env False Nothing (0, []) t r "fail"
          freeReg r
