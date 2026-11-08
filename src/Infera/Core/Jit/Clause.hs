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
import Data.List (nub, sortOn)
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
    upPreds :: [PredKey]
  }

-- | Compile the unit rooted at a predicate, or say why not. The second
-- argument tells whether a goal name and arity is a builtin of the core
-- compiler (anything else that names a program predicate is a call).
planClauseUnit :: Symbols -> (String -> Int -> Bool) -> P.Program -> PredKey -> IO (Either String UnitPlan)
planClauseUnit syms isBuiltin prog entry = case gatherUnit isBuiltin prog entry of
  Left why -> pure (Left why)
  Right preds -> do
    let clausesOf k = maybe [] (IM.elems . P.predClauses) (P.lookupPred k prog)
        terms = concat [S.clauseHead c : concatMap flatten (S.clauseBody c) | (k, _) <- preds, c <- clausesOf k]
    atoms <- forM (nub (concatMap atomsIn terms)) $ \a -> (,) a . fromIntegral . atmWord <$> internAtom syms a
    funs <- forM (nub (concatMap funsIn terms)) $ \(f, n) -> do
      fid <- internFunctor syms f n
      pure ((f, n), fromIntegral (funWord fid n))
    let env = CEnv (M.fromList atoms) (M.fromList funs)
        idx = M.fromList (zip (map fst preds) [0 :: Int ..])
    pure $ do
      let sels = [(k, selectOrNondet p (clausesOf k)) | (k, p) <- preds]
      bodies <- forM (zip [0 :: Int ..] sels) $ \(i, (k, sel)) -> compilePred env idx i k (clausesOf k) sel
      let entrySel = case sels of
            (_, sel) : _ -> sel
            [] -> Selection True [] [] []
          maxArity = maximum (1 : map (snd . fst) preds)
          preflight =
            [ JLoadImm RT0 RState stateBIdx,
              JBranchImm JNe RT0 0 "resume",
              JLoadImm RSP RState stateNStackBaseIdx,
              JMov RE RSP
            ]
              ++ concat [intCheck p "decline" | p <- selInt entrySel]
              ++ concat [groundCheck ("pre_" ++ show p) p "decline" | p <- selGround entrySel]
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
              JBranchImm JEq RT1 0 "rerun",
              JLabel "unit_ok",
              JReturn jitSuccess,
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
      pure (UnitPlan (JitUnit (preflight ++ concat bodies ++ exits)) maxArity (map fst preds))

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
      | IM.size (P.predClauses p) > 16 = Left (show k ++ " has more than 16 clauses")
      | k /= entry && isTrmcCallee k p = Left (show k ++ " is a TRMC list kernel")
      | otherwise = mapM_ (admissibleClause k) (IM.elems (P.predClauses p))
    isTrmcCallee (name, arity) p =
      arity >= 2
        && P.sigDet (P.predInferred p) `elem` [S.Det, S.Semidet]
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
    commitsOnSuccess = P.sigDet inferred == S.Semidet && not (null switch)
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
      | (if isDetOrSemidet then headsExclusive arity ci cj else headsExclusive 1 ci cj) =
          Right ([], [], [(i, disjointPaths (if isDetOrSemidet then arity else 1) ci cj)])
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
                Just ep -> Set.fromList [ (argI, take len sub) | (argI, sub) <- Set.toList ep, len <- [0 .. length sub - 1], not (null sub) ]
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

compilePred :: CEnv -> M.Map PredKey Int -> Int -> PredKey -> [S.Clause] -> Selection -> Either String [JitOp]
compilePred env idx pIx key clauses sel = do
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
      saveArgsOps =
        concat
          [ [JLoadImm RT0 RArgs i, JStoreImm RT0 RE (frameHeader + i)]
            | i <- [0 .. savedArgWords - 1]
          ]
      loadArgsOps =
        concat
          [ [JLoadImm RT0 RE (frameHeader + i), JStoreImm RT0 RArgs i]
            | i <- [0 .. savedArgWords - 1]
          ]
      entry =
        [ JLabel lbl,
          -- RT7 holds the return address. Reserve 8 extra words above RSP for
          -- temporary register spills in unifyWords/not.
          JAddImm RT6 RSP (8 * (frameSize + 8)),
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
                 else []
             )
  blocks <- forM (zip [0 ..] clauses) $ \(k, cl) -> do
    let isLast = k == n - 1
        headFailL = if isLast then "fail" else undoLbl k
        ro = selReadOnly sel !! k
        tempBase = varBase + S.clauseNVars cl
        guardPred = if exclusive then isEarlyGuard else isInlineGuard
    (ops, _) <- runGen 0 varBase tempBase frameSize $ do
      emit [JLabel (clauseLbl k)]
      when (isLast && n > 1) (emit [JLoadImm RHB RE frameHB])
      zipWithM_ (\i a -> matchArg env ro (i, []) a i headFailL (if i == 0 && not isLast then Just (clauseLbl (k + 1)) else Nothing)) [0 ..] (headArgs cl)
      let goals = concatMap flatten (S.clauseBody cl)
          (prefix, rest) = span guardPred goals
      mapM_ (compileGuard env headFailL) prefix
      unless isLast $
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
      compileBody env idx cl (lbl ++ "_c" ++ show k) True rest
    let undo
          | isLast = []
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
                ++ [JMov RHB RH | k + 1 < n - 1]
                ++ [JJump (clauseLbl (k + 1))]
    pure (relabel (lbl ++ "_c" ++ show k ++ "_") ops ++ undo ++ retry)
  pure (entry ++ concat blocks)
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

lbl' :: String -> G Label
lbl' = newLabel . ("L_" ++)

matchArg :: CEnv -> Set.Set (Int, [Int]) -> (Int, [Int]) -> S.Term -> Int -> Label -> Maybe Label -> G ()
matchArg env ro path t i failL mDirectNext = do
  r <- allocReg
  emit [JLoadImm r RArgs i]
  matchTermWith env (Just ro) path t r failL mDirectNext
  freeReg r

matchTerm :: CEnv -> Maybe (Set.Set (Int, [Int])) -> (Int, [Int]) -> S.Term -> Reg -> Label -> G ()
matchTerm env ro path t w failL = matchTermWith env ro path t w failL Nothing

-- | Match a term against the word in @w@ (clobbered), binding unbound cells
-- (write mode) except at read-only paths, where the call goes back to the
-- interpreter. @ro@ is 'Nothing' outside a head. When @mDirectNext@ is
-- @Just nextClauseLbl@ (for the outer tag/functor check of argument 0 before
-- any trail or heap write has occurred), a mismatch jumps directly to
-- @nextClauseLbl@ instead of going through the trail-unwind block.
matchTermWith :: CEnv -> Maybe (Set.Set (Int, [Int])) -> (Int, [Int]) -> S.Term -> Reg -> Label -> Maybe Label -> G ()
matchTermWith env ro path t w failL mDirectNext = case t of
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
      matchTerm env ro (fst path, snd path ++ [k]) a r failL
      freeReg r
    case reverse ordered of
      (k, a) : _ -> do
        emit [JAddImm RT7 s k, JLoadIx s RCells RT7]
        matchTerm env ro (fst path, snd path ++ [k]) a s failL
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
    readOnly = maybe False (Set.member path) ro

-- | Unify two words (both clobbered): equal words, an unbound cell with a
-- constant or structure (with a 1-level occurs check when the structure is
-- not marked ground), two different constants (which fail), and two
-- structures (with 1-level child unification). Deeper nested structures or
-- boxed values rerun on the interpreter.
unifyWords :: Reg -> Reg -> Label -> G ()
unifyWords a b failL = do
  done <- lbl' "u_done"
  aRef <- lbl' "u_aref"
  bRef <- lbl' "u_bref"
  bothRef <- lbl' "u_both"
  bindB <- lbl' "u_bindb"
  aRefBStr <- lbl' "u_aref_bstr"
  bRefAStr <- lbl' "u_bref_astr"
  bindRefStr <- lbl' "u_bind_ref_str"
  bindRefStrOk <- lbl' "u_bind_ref_str_ok"
  occLoop <- lbl' "u_occ_loop"
  occChild <- lbl' "u_occ_child"
  occChildLoop <- lbl' "u_occ_cloop"
  occNext <- lbl' "u_occ_next"
  aStr <- lbl' "u_astr"
  strLoop <- lbl' "u_str_loop"
  strNext <- lbl' "u_str_next"
  strARef <- lbl' "u_str_aref"
  strANonRef <- lbl' "u_str_anonref"
  strABind <- lbl' "u_str_abind"
  strBindB <- lbl' "u_str_bindb"
  strBRef <- lbl' "u_str_bref"
  strBBind <- lbl' "u_str_bbind"
  spillDone <- lbl' "u_spill_done"
  spillFail <- lbl' "u_spill_fail"
  spillRerun <- lbl' "u_spill_rerun"
  let (r0, r1, r2, r3) = case filter (\r -> r /= a && r /= b) workRegs of
        x0 : x1 : x2 : x3 : _ -> (x0, x1, x2, x3)
        _ -> (RT0, RT1, RT2, RT3)
      spill = [JStoreImm r0 RSP 0, JStoreImm r1 RSP 1, JStoreImm r2 RSP 2, JStoreImm r3 RSP 3]
      unspill = [JLoadImm r0 RSP 0, JLoadImm r1 RSP 1, JLoadImm r2 RSP 2, JLoadImm r3 RSP 3]
  emit $
    [ JDeref a a,
      JDeref b b,
      JBranchCmp JEq a b done,
      JTagOf RT7 a,
      JBranchImm JEq RT7 (fromIntegral tagRef) aRef,
      JTagOf RT7 b,
      JBranchImm JEq RT7 (fromIntegral tagRef) bRef,
      JTagOf RT7 a,
      JBranchImm JEq RT7 (fromIntegral tagStr) aStr,
      JBranchImm JEq RT7 (fromIntegral tagBox) "rerun",
      JJump failL,
      JLabel aRef,
      JTagOf RT7 b,
      JBranchImm JEq RT7 (fromIntegral tagRef) bothRef,
      JBranchImm JEq RT7 (fromIntegral tagStr) aRefBStr,
      JValOf a a,
      JBindRef a b "rerun",
      JJump done,
      JLabel bRef,
      JTagOf RT7 a,
      JBranchImm JEq RT7 (fromIntegral tagStr) bRefAStr,
      JValOf b b,
      JBindRef b a "rerun",
      JJump done,
      JLabel bothRef,
      JBranchCmp JLt a b bindB,
      JValOf a a,
      JBindRef a b "rerun",
      JJump done,
      JLabel bindB,
      JValOf b b,
      JBindRef b a "rerun",
      JJump done,
      JLabel bRefAStr,
      JMov RT7 a,
      JMov a b,
      JMov b RT7,
      JLabel aRefBStr,
      JLabel bindRefStr
    ]
      ++ spill
      ++ [ JValOf r0 b,
           JLoadIx r1 RCells r0,
           JMovImm RT7 (fromIntegral groundBit),
           JAnd RT7 r1 RT7,
           JBranchImm JNe RT7 0 bindRefStrOk,
           JValOf r1 r1,
           JMovImm RT7 0x7FFFF,
           JAnd r1 r1 RT7,
           JLabel occLoop,
           JBranchImm JEq r1 0 bindRefStrOk,
           JAddImm r0 r0 1,
           JLoadIx r2 RCells r0,
           JDeref r2 r2,
           JBranchCmp JEq r2 a spillFail,
           JTagOf RT7 r2,
           JBranchImm JNe RT7 (fromIntegral tagStr) occNext,
           JValOf r3 r2,
           JLoadIx r2 RCells r3,
           JMovImm RT7 (fromIntegral groundBit),
           JAnd RT7 r2 RT7,
           JBranchImm JNe RT7 0 occNext,
           JBranchImm JNe r1 1 occChild,
           JMov r0 r3,
           JValOf r1 r2,
           JMovImm RT7 0x7FFFF,
           JAnd r1 r1 RT7,
           JJump occLoop,
           JLabel occChild,
           JValOf r2 r2,
           JMovImm RT7 0x7FFFF,
           JAnd r2 r2 RT7,
           JLabel occChildLoop,
           JBranchImm JEq r2 0 occNext,
           JAddImm r3 r3 1,
           JLoadIx RT7 RCells r3,
           JDeref RT7 RT7,
           JBranchCmp JEq RT7 a spillFail,
           JTagOf RT7 RT7,
           JBranchImm JEq RT7 (fromIntegral tagStr) spillRerun,
           JSubImm r2 r2 1,
           JJump occChildLoop,
           JLabel occNext,
           JSubImm r1 r1 1,
           JJump occLoop,
           JLabel bindRefStrOk,
           JValOf a a,
           JBindRef a b spillRerun,
           JJump spillDone,
           JLabel aStr,
           JTagOf RT7 b,
           JBranchImm JNe RT7 (fromIntegral tagStr) failL
         ]
      ++ spill
      ++ [ JValOf a a,
           JValOf b b,
           JLoadIx r0 RCells a,
           JLoadIx r1 RCells b,
           JMovImm RT7 (complement (fromIntegral groundBit)),
           JAnd r0 r0 RT7,
           JAnd r1 r1 RT7,
           JBranchCmp JNe r0 r1 spillFail,
           JValOf r0 r0,
           JMovImm RT7 0x7FFFF,
           JAnd r0 r0 RT7,
           JLabel strLoop,
           JBranchImm JEq r0 0 spillDone,
           JAddImm a a 1,
           JAddImm b b 1,
           JLoadIx r1 RCells a,
           JDeref r1 r1,
           JLoadIx r2 RCells b,
           JDeref r2 r2,
           JBranchCmp JEq r1 r2 strNext,
           JTagOf r3 r1,
           JTagOf RT7 r2,
           JBranchImm JEq r3 (fromIntegral tagRef) strARef,
           JBranchImm JEq RT7 (fromIntegral tagRef) strBRef,
           JBranchCmp JNe r3 RT7 spillFail,
           JBranchImm JEq r3 (fromIntegral tagStr) spillRerun,
           JBranchImm JEq r3 (fromIntegral tagBox) spillRerun,
           JJump spillFail,
           JLabel strARef,
           JBranchImm JNe RT7 (fromIntegral tagRef) strANonRef,
           JBranchCmp JLt r1 r2 strBindB,
           JValOf r1 r1,
           JBindRef r1 r2 spillRerun,
           JJump strNext,
           JLabel strBindB,
           JValOf r2 r2,
           JBindRef r2 r1 spillRerun,
           JJump strNext,
           JLabel strANonRef,
           JBranchImm JNe RT7 (fromIntegral tagStr) strABind,
           JValOf r3 r2,
           JLoadIx r3 RCells r3,
           JMovImm RT7 (fromIntegral groundBit),
           JAnd r3 r3 RT7,
           JBranchImm JEq r3 0 spillRerun,
           JLabel strABind,
           JValOf r1 r1,
           JBindRef r1 r2 spillRerun,
           JJump strNext,
           JLabel strBRef,
           JBranchImm JNe r3 (fromIntegral tagStr) strBBind,
           JValOf r3 r1,
           JLoadIx r3 RCells r3,
           JMovImm RT7 (fromIntegral groundBit),
           JAnd r3 r3 RT7,
           JBranchImm JEq r3 0 spillRerun,
           JLabel strBBind,
           JValOf r2 r2,
           JBindRef r2 r1 spillRerun,
           JLabel strNext,
           JSubImm r0 r0 1,
           JJump strLoop,
           JLabel spillFail
         ]
      ++ unspill
      ++ [ JJump failL,
           JLabel spillRerun
         ]
      ++ unspill
      ++ [ JJump "rerun",
           JLabel spillDone
         ]
      ++ unspill
      ++ [JLabel done]

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
              then emit [JLoadImm r RE sv]
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
                      unless staticNon (groundOrClear w off fw)
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
      emit [JSubImm b RH totalOff, JMkWord b b tagStr]
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
      g <- allocReg
      u <- allocReg
      okL <- lbl' "gnd"
      nonL <- lbl' "non"
      emit
        [ JMov g w,
          JDeref g g,
          JTagOf u g,
          JBranchImm JEq u (fromIntegral tagRef) nonL,
          JBranchImm JNe u (fromIntegral tagStr) okL,
          JValOf g g,
          JLoadIx g RCells g,
          JMovImm u (fromIntegral groundBit),
          JAnd g g u,
          JBranchImm JNe g 0 okL,
          JLabel nonL,
          JSubImm u RH off,
          JMovImm g fw,
          JStoreIx g RCells u,
          JLabel okL
        ]
      freeReg u
      freeReg g

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

-- | Structural equality (@==@) between two operands, branching to @eqL@ when
-- equal and @neL@ when distinct; reruns on the interpreter only when both are
-- boxed values or both are structures with the same functor at different cells.
compileEquivBranch :: CEnv -> S.Term -> S.Term -> Label -> Label -> G ()
compileEquivBranch env a b eqL neL = do
  ra <- loadOperand a
  rb <- loadOperand b
  t1 <- allocReg
  t2 <- allocReg
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
    ra <- atomic a
    rb <- atomic b
    emit [JBranchCmp JEq ra rb failL]
    freeReg rb
    freeReg ra
  S.Compound "equiv" [a, b]
    | atomicOk a && atomicOk b -> do
        okL <- lbl' "eq_ok"
        compileEquivBranch env a b okL failL
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
    atomic t = do
      r <- allocReg
      case t of
        S.Var v | v >= 0 -> do
          seen <- isSeen v
          unless seen (decline "!= on an unbound variable")
          sv <- slot v
          okL <- lbl' "atm"
          emit
            [ JLoadImm r RE sv,
              JDeref r r,
              JTagOf RT7 r,
              JBranchImm JEq RT7 (fromIntegral tagRef) "rerun",
              JBranchImm JEq RT7 (fromIntegral tagStr) "rerun",
              JBranchImm JEq RT7 (fromIntegral tagBox) "rerun",
              JLabel okL
            ]
        _ -> case constWord env t of
          Just cw -> emit [JMovImm r cw]
          Nothing -> decline "!= on a term outside the fragment"
      pure r

compileNegatedTest :: CEnv -> Label -> S.Term -> G ()
compileNegatedTest env failL = \case
  S.Compound "equiv" [a, b] | atomicOk a && atomicOk b -> do
    okL <- lbl' "neq_ok"
    compileEquivBranch env a b failL okL
    emit [JLabel okL]
  S.Compound "neq" [a, b] | atomicOk a && atomicOk b -> do
    okL <- lbl' "not_neq_ok"
    compileGuard env okL (S.Compound "neq" [a, b])
    emit [JJump failL, JLabel okL]
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
  S.IntLit _ -> when ( (mTag == Just tagInt) == invert ) (emit [JJump failL])
  S.Atom _ -> when ( (mTag == Just tagAtm) == invert ) (emit [JJump failL])
  S.CharLit _ -> when ( (mTag == Just tagChr) == invert ) (emit [JJump failL])
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
compileBody :: CEnv -> M.Map PredKey Int -> S.Clause -> String -> Bool -> [S.Term] -> G ()
compileBody env idx cl base allowTail = go
  where
    allClauseVars = allVarsIn (S.clauseHead cl) ++ concatMap allVarsIn (concatMap flatten (S.clauseBody cl))
    varOccurrences v = length (filter (== v) allClauseVars)
    go [] = when allowTail $ do
      skipL <- lbl' "keep_sp"
      emit
        [ JLoadImm RT7 RE frameRet,
          JLoadImm RT0 RState stateBIdx,
          JBranchCmp JLe RE RT0 skipL,
          JMov RSP RE,
          JLabel skipL,
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
        compileBody env idx cl (base ++ "_once") False innerGoals
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
            [ JAddImm RT6 RSP (8 * (frameHeader + 8)),
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
          compileBody env idx cl (base ++ "_not") False innerGoals
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
            target <- maybe (decline ("call outside the unit: " ++ show k)) pure (M.lookup k idx)
            forM_ (zip [0 ..] (callArgs g)) $ \(i, a) -> do
              r <- buildTerm env a
              emit [JStoreImm r RArgs i]
              freeReg r
            if null gs && allowTail
              then do
                skipL <- lbl' "keep_tail_sp"
                emit
                  [ JLoadImm RT7 RE frameRet,
                    JLoadImm RT0 RState stateBIdx,
                    JBranchCmp JLe RE RT0 skipL,
                    JMov RSP RE,
                    JLabel skipL,
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
          matchTerm env Nothing (0, []) t r "fail"
          freeReg r
