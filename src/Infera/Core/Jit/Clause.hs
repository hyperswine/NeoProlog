{-# LANGUAGE LambdaCase #-}

-- | The clause compiler: whole predicates to native code, increment 1 of
-- @docs/2026-11-06-CLAUSE-COMPILER.md@ ("det islands").
--
-- A unit is an entry predicate and every predicate it reaches. Each
-- predicate is compiled clause by clause: head matching in read and write
-- mode, inline arithmetic and comparisons, unification with a term, and
-- calls to the unit's other predicates. Clause variables live in an
-- environment frame on a native stack (not the C stack), and a call stores
-- its return address in the callee's frame.
--
-- A call tries its clauses in order and commits to the first whose head and
-- leading guards hold; a clause that fails before that point is undone from
-- the trail. Committing is what the interpreter does only when no later
-- clause could also match, so every predicate in a unit must prove that
-- (see 'selection'). With nothing left to retry after a commit, a native
-- call never leaves a choice point, and anything native code cannot
-- finish is rerun on the interpreter from the call's entry.
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
import Infera.Core.Store (Symbols, atmWord, chrWord, funWord, groundBit, internAtom, internFunctor, intWord, tagBox, tagInt, tagRef, tagStr)
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
      sels <- forM preds $ \(k, p) -> (,) k <$> selection p (clausesOf k)
      bodies <- forM (zip [0 :: Int ..] sels) $ \(i, (k, sel)) -> compilePred env idx i k (clausesOf k) sel
      let entrySel = case sels of
            (_, sel) : _ -> sel
            [] -> Selection [] []
          maxArity = maximum (1 : map (snd . fst) preds)
          preflight =
            [JLoadImm RSP RState stateNStackBaseIdx, JMov RE RSP]
              ++ concat [groundCheck ("pre_" ++ show p) p "decline" | p <- selGround entrySel]
              ++ [JLoadLabel RT7 "unit_done", JJump (predLabel 0)]
          exits =
            [ JLabel "unit_done",
              JReturn jitSuccess,
              JLabel "fail",
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
          let callees = [c | cl <- IM.elems (P.predClauses p), g <- concatMap flatten (S.clauseBody cl), Just c <- [callKey g]]
          gather (queue ++ callees) ((k, p) : done)
    admissible k p
      | not (null (P.predDecls p)) = Left (show k ++ " has declared contracts")
      | P.predIsTabled prog p = Left (show k ++ " is tabled")
      | P.nameHasFlag prog (fst k) S.FlagDynamic = Left (show k ++ " is dynamic")
      | snd k > 8 = Left (show k ++ " has more than 8 arguments")
      | IM.null (P.predClauses p) = Left (show k ++ " has no clauses")
      | IM.size (P.predClauses p) > 16 = Left (show k ++ " has more than 16 clauses")
      | otherwise = mapM_ (admissibleClause k) (IM.elems (P.predClauses p))
    admissibleClause k cl = do
      unless (all termOk (headArgs cl)) (Left (show k ++ ": head outside the fragment"))
      forM_ (concatMap flatten (S.clauseBody cl)) $ \g ->
        unless (goalOk g) (Left (show k ++ ": goal outside the fragment: " ++ take 60 (show g)))
    goalOk g = case g of
      S.Atom "true" -> True
      S.Compound "is" [l, e] -> termOk l && exprOk e
      S.Compound op [a, b] | op `elem` ["gt", "lt", "gte", "lte"] -> exprOk a && exprOk b
      S.Compound "neq" [a, b] -> atomicOk a && atomicOk b
      S.Compound "unify" [a, b] -> termOk a && termOk b
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

-- | Terms native code builds and matches: variables, immediate constants,
-- and structures of them. An arithmetic functor as data is evaluated by the
-- interpreter in some positions, so it is left out.
termOk :: S.Term -> Bool
termOk = \case
  S.Var _ -> True
  S.Atom _ -> True
  S.IntLit k -> fits k
  S.CharLit _ -> True
  S.Compound f as -> (f, length as) `notElem` arithNames && f /= "$path" && all termOk as
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

-- | How a predicate's calls may commit: the arguments that must be ground
-- at the call, and per clause the head paths that must not be bound by the
-- head (a path is the argument index, then 1-based child positions).
data Selection = Selection
  { selGround :: [Int],
    selReadOnly :: [Set.Set (Int, [Int])]
  }

-- | Leading goals the interpreter evaluates before a clause can produce
-- anything: arithmetic and comparison guards. A clause whose prefix fails
-- moves to the next clause in native code too.
isGuard :: S.Term -> Bool
isGuard = \case
  S.Atom "true" -> True
  S.Compound "is" _ -> True
  S.Compound op [_, _] -> op `elem` ["gt", "lt", "gte", "lte", "neq"]
  _ -> False

guardPrefix :: S.Clause -> [S.Term]
guardPrefix = takeWhile isGuard . concatMap flatten . S.clauseBody

-- | Committing to clause @i@ after its head and guard prefix is safe when
-- every later clause @j@ cannot match then, and could not raise an error
-- the interpreter would raise before failing it:
--
-- * the two heads differ at an input path, which clause @i@ must then match
--   without binding (a bound value there fails clause @j@'s head);
-- * the module's integer analysis ('clausesExclusive') or determinism
--   inference ('Infer.exclusive', with the positions it names ground at the
--   call) proves the heads and prefixes exclusive, and clause @j@'s prefix
--   evaluates only values clause @i@ evaluated or pinned to an integer;
-- * the interpreter commits on success too (inferred semidet, switch
--   arguments ground at the call) and clause @i@ is all head and guards.
--
-- Output arguments (mode @=>@) are left out of every proof: they are
-- usually unbound, so a constant there would be bound, not tested.
selection :: P.Pred -> [S.Clause] -> Either String Selection
selection p clauses = do
  grounds <- forM [(i, j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1]] pair
  let ro = [if i == n - 1 then Set.empty else readOnlyPaths (masked !! i) | i <- [0 .. n - 1]]
  pure (Selection (nub (concat grounds)) ro)
  where
    n = length clauses
    key = P.predKey p
    arity = snd key
    inferred = P.predInferred p
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
    pair (i, j)
      | headsExclusive arity ci cj = Right []
      | laterRaisesNothingNew arity ci cj, evalSafe ci cj, clausesExclusive arity ci cj = Right guarded
      | laterRaisesNothingNew arity ci cj, evalSafe ci cj, Just ps <- I.exclusive ci cj, all isInput ps = Right (nub (ps ++ guarded))
      | commitsOnSuccess, allGuards (clauses !! i) = Right switch
      | otherwise = Left (show key ++ ": clauses " ++ show (i + 1) ++ " and " ++ show (j + 1) ++ " may both match")
      where
        ci = masked !! i
        cj = masked !! j
        -- A guard proof assumes both clauses see the same values. Head
        -- matching can bind an unbound argument through an alias
        -- (@p U U@), so the arguments the guards read must be ground.
        guarded = case (evaluatedPaths ci, evaluatedPaths cj) of
          (Just ei, Just ej) -> nub (map fst (Set.toList (ei `Set.union` ej)))
          _ -> []
    allGuards cl = all isGuard (concatMap flatten (S.clauseBody cl))

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

-- Frame layout, in words from RE: the caller's frame, the return address,
-- the trail and heap marks of the call (for retrying clauses), then one
-- slot per clause variable.
frameLink, frameRet, frameTR, frameH, frameVars :: Int
frameLink = 0
frameRet = 1
frameTR = 2
frameH = 3
frameVars = 4

slot :: S.VarId -> Int
slot v = frameVars + v

predLabel :: Int -> Label
predLabel i = "p" ++ show i

data GS = GS
  { gsNext :: !Int,
    gsSeen :: !(Set.Set S.VarId),
    gsFree :: ![Reg],
    gsOps :: ![[JitOp]]
  }

type G = StateT GS (Either String)

emit :: [JitOp] -> G ()
emit ops = modify' (\s -> s {gsOps = ops : gsOps s})

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

runGen :: Int -> G () -> Either String ([JitOp], Int)
runGen next g = do
  s <- execStateT g (GS next Set.empty workRegs [])
  pure (concat (reverse (gsOps s)), gsNext s)

compilePred :: CEnv -> M.Map PredKey Int -> Int -> PredKey -> [S.Clause] -> Selection -> Either String [JitOp]
compilePred env idx pIx key clauses sel = do
  let lbl = predLabel pIx
      n = length clauses
      frameSize = frameVars + maximum (0 : map S.clauseNVars clauses)
      clauseLbl k = lbl ++ "_c" ++ show k
      undoLbl k = lbl ++ "_u" ++ show k
      entry =
        [ JLabel lbl,
          -- RT7 holds the return address.
          JAddImm RT6 RSP (8 * frameSize),
          JLoadImm RT5 RState stateNStackLimIdx,
          JBranchCmp JGt RT6 RT5 "stackfull",
          JStoreImm RE RSP frameLink,
          JStoreImm RT7 RSP frameRet,
          JMov RE RSP,
          JMov RSP RT6
        ]
          ++ concat [groundCheck (lbl ++ "_g" ++ show p) p "rerun" | p <- selGround sel]
          -- Bindings a failed clause made must be undone before the next
          -- clause runs, so cells older than the call are trailed.
          ++ (if n > 1 then [JStoreImm RTR RE frameTR, JStoreImm RH RE frameH, JMov RHB RH] else [])
  blocks <- forM (zip [0 ..] clauses) $ \(k, cl) -> do
    let isLast = k == n - 1
        failL = if isLast then "fail" else undoLbl k
        ro = selReadOnly sel !! k
    (ops, _) <- runGen 0 $ do
      emit [JLabel (clauseLbl k)]
      when (isLast && n > 1) (emit [JLoadImm RHB RState stateHBIdx])
      zipWithM_ (\i a -> matchArg env ro (i, []) a i failL) [0 ..] (headArgs cl)
      let goals = concatMap flatten (S.clauseBody cl)
          (prefix, rest) = span isGuard goals
      mapM_ (compileGuard env failL) prefix
      -- Commit: the trail entries this clause made for cells younger than
      -- the unit's entry were only for retrying, so they are dropped.
      unless isLast $ do
        loopL <- lbl' "keep"
        nextL <- lbl' "keep_next"
        doneL <- lbl' "keep_done"
        emit
          [ JLoadImm RHB RState stateHBIdx,
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
      compileBody env idx (lbl ++ "_c" ++ show k) rest
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
    pure (relabel (lbl ++ "_c" ++ show k ++ "_") ops ++ undo)
  pure (entry ++ concat blocks)
  where
    _ = key
    -- Labels made inside a clause are local to it; global ones are kept.
    relabel pre = map $ \case
      JLabel l | local l -> JLabel (pre ++ l)
      JJump l | local l -> JJump (pre ++ l)
      JBranchCmp c a b l | local l -> JBranchCmp c a b (pre ++ l)
      JBranchImm c a k l | local l -> JBranchImm c a k (pre ++ l)
      JLoadLabel r l | local l -> JLoadLabel r (pre ++ l)
      op -> op
    local l = take 2 l == "L_"

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

matchArg :: CEnv -> Set.Set (Int, [Int]) -> (Int, [Int]) -> S.Term -> Int -> Label -> G ()
matchArg env ro path t i failL = do
  r <- allocReg
  emit [JLoadImm r RArgs i]
  matchTerm env (Just ro) path t r failL
  freeReg r

-- | Match a term against the word in @w@ (clobbered), binding unbound cells
-- (write mode) except at read-only paths, where the call goes back to the
-- interpreter. @ro@ is 'Nothing' outside a head.
matchTerm :: CEnv -> Maybe (Set.Set (Int, [Int])) -> (Int, [Int]) -> S.Term -> Reg -> Label -> G ()
matchTerm env ro path t w failL = case t of
  S.Var v
    | v < 0 -> pure ()
    | otherwise -> do
        seen <- isSeen v
        if seen
          then do
            r <- allocReg
            emit [JLoadImm r RE (slot v)]
            unifyWords r w failL
            freeReg r
          else emit [JStoreImm w RE (slot v)] >> markSeen v
  S.Compound f as -> do
    readL <- lbl' "read"
    doneL <- lbl' "done"
    emit [JDeref w w, JTagOf RT7 w, JBranchImm JEq RT7 (fromIntegral tagStr) readL, JBranchImm JNe RT7 (fromIntegral tagRef) failL]
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
        JBranchCmp JNe RT7 tmp failL
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
      okL <- lbl' "ok"
      emit [JDeref w w, JMovImm RT7 cw, JBranchCmp JEq w RT7 okL, JTagOf RT7 w, JBranchImm JNe RT7 (fromIntegral tagRef) failL]
      if readOnly
        then emit [JJump "rerun"]
        else emit [JValOf w w, JMovImm RT7 cw, JBindRef w RT7 "rerun"]
      emit [JLabel okL]
    Nothing -> decline ("constant outside the fragment: " ++ show t)
  where
    readOnly = maybe False (Set.member path) ro

-- | Unify two words (both clobbered) where that needs no walk: equal
-- words, an unbound cell with anything but a structure not marked ground,
-- and two different constants (which fail). Two unbound cells bind the
-- younger to the older, as 'Store.unify' does; anything else goes to the
-- interpreter.
unifyWords :: Reg -> Reg -> Label -> G ()
unifyWords a b failL = do
  done <- lbl' "u_done"
  aRef <- lbl' "u_aref"
  bRef <- lbl' "u_bref"
  both <- lbl' "u_both"
  bindB <- lbl' "u_bindb"
  let nonGroundStr r = do
        okL <- lbl' "u_gnd"
        t <- allocReg
        emit
          [ JTagOf RT7 r,
            JBranchImm JNe RT7 (fromIntegral tagStr) okL,
            JValOf t r,
            JLoadIx t RCells t,
            JMovImm RT7 (fromIntegral groundBit),
            JAnd t t RT7,
            JBranchImm JEq t 0 "rerun",
            JLabel okL
          ]
        freeReg t
  emit
    [ JDeref a a,
      JDeref b b,
      JBranchCmp JEq a b done,
      JTagOf RT7 a,
      JBranchImm JEq RT7 (fromIntegral tagRef) aRef,
      JTagOf RT7 b,
      JBranchImm JEq RT7 (fromIntegral tagRef) bRef,
      JTagOf RT7 a,
      JBranchImm JEq RT7 (fromIntegral tagStr) "rerun",
      JBranchImm JEq RT7 (fromIntegral tagBox) "rerun",
      JTagOf RT7 b,
      JBranchImm JEq RT7 (fromIntegral tagStr) "rerun",
      JBranchImm JEq RT7 (fromIntegral tagBox) "rerun",
      JJump failL,
      JLabel aRef,
      JTagOf RT7 b,
      JBranchImm JEq RT7 (fromIntegral tagRef) both
    ]
  nonGroundStr b
  emit [JValOf a a, JBindRef a b "rerun", JJump done, JLabel bRef]
  nonGroundStr a
  emit
    [ JValOf b b,
      JBindRef b a "rerun",
      JJump done,
      JLabel both,
      JBranchCmp JLt a b bindB,
      JValOf a a,
      JBindRef a b "rerun",
      JJump done,
      JLabel bindB,
      JValOf b b,
      JBindRef b a "rerun",
      JLabel done
    ]

-- | Before binding the unbound cell in @w@ to a new structure holding the
-- values of earlier variables: a variable that is the cell itself fails
-- (occurs check); one holding a structure not marked ground goes to the
-- interpreter, which walks it.
occursChecks :: [S.VarId] -> Reg -> Label -> G ()
occursChecks vs w failL = forM_ vs $ \v -> do
  t <- allocReg
  okL <- lbl' "occ"
  emit
    [ JLoadImm t RE (slot v),
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
            r <- allocReg
            if seen
              then emit [JLoadImm r RE (slot v)]
              else do
                emit [JMkWord r RH tagRef, JStoreIx r RCells RH, JAddImm RH RH 1, JStoreImm r RE (slot v)]
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
    -- The structure's cells, then its nested structures above them. The
    -- functor is written with the ground memo set and rewritten without it
    -- when an argument is not ground now, as 'structureWord' decides.
    buildStruct f as = do
      let n = length as
          fw = funW env f n
      seen0 <- gets gsSeen
      -- Nested structures first, so a chain of them holds one register.
      kids <- forM [a | a@(S.Compound _ _) <- as] $ \case
        S.Compound g bs -> buildStruct g bs
        _ -> decline "unreachable"
      let fresh = \case
            S.Var v -> v < 0 || not (Set.member v seen0)
            _ -> False
          staticNon = any fresh as || any ((== Just False) . snd) kids
      b <- allocReg
      emit [JMov b RH, JAddImm RH RH (n + 1)]
      emit [JMovImm RT7 (if staticNon then fw else fw .|. fromIntegral groundBit), JStoreIx RT7 RCells b]
      let store k r = do
            a' <- allocReg
            emit [JAddImm a' b k, JStoreIx r RCells a']
            freeReg a'
          fill _ [] _ = pure ()
          fill k (a : rest) ks = case a of
            S.Var v
              | v < 0 -> freshCell k >> fill (k + 1) rest ks
              | otherwise -> do
                  seen <- isSeen v
                  if not seen
                    then do
                      freshCell k
                      emit [JStoreImm RT7 RE (slot v)]
                      markSeen v
                    else do
                      w <- allocReg
                      emit [JLoadImm w RE (slot v)]
                      store k w
                      unless staticNon (groundOrClear w b fw)
                      freeReg w
                  fill (k + 1) rest ks
            S.Compound _ _ -> case ks of
              (cb, childStatic) : ks' -> do
                store k cb
                unless staticNon $ case childStatic of
                  Just True -> pure ()
                  Just False -> emit [JMovImm RT7 fw, JStoreIx RT7 RCells b]
                  Nothing -> groundOrClear cb b fw
                freeReg cb
                fill (k + 1) rest ks'
              [] -> decline "unreachable"
            c -> case constWord env c of
              Just cw -> do
                a' <- allocReg
                emit [JAddImm a' b k, JMovImm RT7 cw, JStoreIx RT7 RCells a']
                freeReg a'
                fill (k + 1) rest ks
              Nothing -> decline ("constant outside the fragment: " ++ show c)
          -- An unbound argument cell; its word is left in RT7.
          freshCell k = do
            a' <- allocReg
            emit [JAddImm a' b k, JMkWord RT7 a' tagRef, JStoreIx RT7 RCells a']
            freeReg a'
      fill (1 :: Int) as kids
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
    -- Clear the memo in functor cell @b@ unless the word in @w@ is ground now.
    groundOrClear w b fw = do
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
          JMovImm g fw,
          JStoreIx g RCells b,
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
    r <- allocReg
    emit [JLoadImm r RE (slot v), JDeref r r, JTagOf RT7 r, JBranchImm JNe RT7 (fromIntegral tagInt) "rerun", JValOf r r]
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

compileGuard :: CEnv -> Label -> S.Term -> G ()
compileGuard env failL = \case
  S.Atom "true" -> pure ()
  S.Compound "is" [lhs, e] -> do
    r <- evalExpr e
    case lhs of
      S.IntLit k -> emit [JBranchImm JNe r (fromIntegral k) failL]
      S.Var v | v >= 0 -> do
        seen <- isSeen v
        emit [JMkWord r r tagInt]
        if not seen
          then emit [JStoreImm r RE (slot v)] >> markSeen v
          else do
            t <- allocReg
            okL <- lbl' "is"
            emit
              [ JLoadImm t RE (slot v),
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
  -- Structural, and decided only when both sides are ground: here both
  -- must be immediate constants, or the interpreter decides.
  S.Compound "neq" [a, b] -> do
    ra <- atomic a
    rb <- atomic b
    emit [JBranchCmp JEq ra rb failL]
    freeReg rb
    freeReg ra
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
          okL <- lbl' "atm"
          emit
            [ JLoadImm r RE (slot v),
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

-- | The rest of a clause body after its commit: guards fail the whole unit
-- (nothing is left to retry), calls go to the unit's predicates, and the
-- last call is a jump.
compileBody :: CEnv -> M.Map PredKey Int -> String -> [S.Term] -> G ()
compileBody env idx base goals = go goals
  where
    go [] = emit proceed
    go (g : gs) = case g of
      S.Compound "unify" [a, b] -> unifyGoal a b >> go gs
      _
        | isGuard g -> compileGuard env "fail" g >> go gs
        | otherwise -> do
            let k = (calleeName g, length (callArgs g))
            target <- maybe (decline ("call outside the unit: " ++ show k)) pure (M.lookup k idx)
            forM_ (zip [0 ..] (callArgs g)) $ \(i, a) -> do
              r <- buildTerm env a
              emit [JStoreImm r RArgs i]
              freeReg r
            if null gs
              then emit [JLoadImm RT7 RE frameRet, JMov RSP RE, JLoadImm RE RE frameLink, JJump (predLabel target)]
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
    proceed = [JLoadImm RT7 RE frameRet, JMov RSP RE, JLoadImm RE RE frameLink, JJumpReg RT7]
    calleeName = \case
      S.Atom f -> f
      S.Compound f _ -> f
      _ -> ""
    unifyGoal a b = case (a, b) of
      (S.Var v, t) | v >= 0 -> withVar v t
      (t, S.Var v) | v >= 0 -> withVar v t
      _ -> decline "unification of two non-variables"
    withVar v t = do
      seen <- isSeen v
      if not seen
        then do
          when (v `elem` termVarIds t) (decline "cyclic unification")
          r <- buildTerm env t
          emit [JStoreImm r RE (slot v)]
          markSeen v
          freeReg r
        else do
          r <- allocReg
          emit [JLoadImm r RE (slot v)]
          matchTerm env Nothing (0, []) t r "fail"
          freeReg r
