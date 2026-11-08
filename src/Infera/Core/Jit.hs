{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE LambdaCase #-}

-- | Step 3 + Horizon 1 + Horizon 4 native JIT tier for deterministic predicates.
--
-- Adapted from fprisc:compiler/Sol/HandJIT.hs and Sol/JitCore.hs
-- Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
module Infera.Core.Jit
  ( JitKernel (..),
    ParamRole (..),
    jitEnabled,
    jitDebugOn,
    compileJitKernel,
    compileGeneralTailJit,
    invokeJitKernel,
    invokeJitKernelWith,
    resumeClauseUnit,
    invokeScanKernel,
    scanShape,
    runNativeUnit,
  )
where

import Control.Monad (foldM, forM_, when)
import Data.Bits (complement, shiftL, (.|.))
import qualified Data.IntMap.Strict as IM
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.Int (Int64)
import Data.List (nub)
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Data.Word (Word8)
import Foreign.C.Types (CInt (..), CLong (..))
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrArray, withForeignPtr)
import Foreign.Marshal.Array (withArray, withArrayLen)
import Foreign.Ptr (FunPtr, Ptr, castPtrToFunPtr, intPtrToPtr, nullFunPtr, nullPtr, ptrToIntPtr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import Infera.Core.Jit.AsmA64 (assembleA64)
import Infera.Core.Jit.AsmX64 (assembleX64)
import Infera.Core.Jit.Clause (UnitPlan (..), admitClauseUnit, planClauseUnit)
import Infera.Core.Jit.Exclusive
import Infera.Core.Jit.IR
import Infera.Core.Store
import Infera.Error (PredKey)
import qualified Infera.Infer as I
import qualified Infera.Program as P
import qualified Infera.Syntax as S
import System.Environment (lookupEnv)
import System.IO (IOMode (..), hPutBuf, hPutStrLn, stderr, withBinaryFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Info (arch)

foreign import ccall unsafe "infera_jit_alloc"
  c_inferaJitAlloc :: Ptr Word8 -> CLong -> IO (Ptr Word8)

foreign import ccall unsafe "infera_jit_has_sse41"
  c_inferaJitHasSse41 :: IO CInt

type NativeFn = Ptr Int64 -> Ptr Int64 -> Ptr Int64 -> IO Int64

foreign import ccall unsafe "dynamic"
  callNativeFn :: FunPtr NativeFn -> NativeFn

jitEnabled :: Bool
jitEnabled = unsafePerformIO $ do
  env <- lookupEnv "INFERA_JIT"
  case env of
    Just "0" -> pure False
    _ -> case arch of
      "aarch64" -> pure True
      "x86_64" -> (/= 0) <$> c_inferaJitHasSse41
      _ -> pure False
{-# NOINLINE jitEnabled #-}

jitDebugOn :: Bool
jitDebugOn = unsafePerformIO (maybe False (== "1") <$> lookupEnv "INFERA_JIT_DEBUG")
{-# NOINLINE jitDebugOn #-}

jitXcheckDir :: Maybe FilePath
jitXcheckDir = unsafePerformIO (lookupEnv "INFERA_JIT_XCHECK")
{-# NOINLINE jitXcheckDir #-}

xcheckSeq :: IORef Int
xcheckSeq = unsafePerformIO (newIORef 0)
{-# NOINLINE xcheckSeq #-}

jitDebug :: String -> IO ()
jitDebug msg = when jitDebugOn (hPutStrLn stderr ("[infera-jit] " ++ msg))

data JitKernel = JitKernel
  { jkKey :: !PredKey,
    jkArity :: !Int,
    jkFunPtr :: !(FunPtr NativeFn),
    jkAddr :: !Int64,
    jkCellsPerIter :: !Int,
    jkScratch :: !(ForeignPtr Int64),
    -- | a list search ('scanShape'): the list argument's position; -1 for
    -- a deterministic kernel; -2 for a clause unit ("Infera.Core.Jit.Clause");
    -- -3 for a clause unit not compiled yet
    jkScan :: !Int,
    -- | a clause unit's native stack and its size in words
    jkStack :: !(Maybe (IORef (ForeignPtr Int64, Int))),
    -- | for a deferred clause unit (@jkScan == -3@): the unit, compiled
    -- when the predicate is first called (lazy on purpose)
    jkLazy :: Maybe JitKernel
  }

assembleHost :: JitUnit -> [Word8]
assembleHost unit = case arch of
  "aarch64" -> assembleA64 unit
  "x86_64" -> assembleX64 unit
  _ -> []

-- | Assemble a unit for this host and call it once with the given state,
-- args and budgets blocks, for tests of single ops. 'Nothing' where the JIT
-- is off or the host has no backend. The code is never freed.
runNativeUnit :: JitUnit -> Ptr Int64 -> Ptr Int64 -> Ptr Int64 -> IO (Maybe Int64)
runNativeUnit unit statePtr argsPtr budgetsPtr
  | not jitEnabled || null bytes = pure Nothing
  | otherwise = do
      ptr <- withArray bytes $ \pb -> c_inferaJitAlloc pb (fromIntegral (length bytes))
      if ptr == nullPtr
        then pure Nothing
        else Just <$> callNativeFn (castPtrToFunPtr ptr) statePtr argsPtr budgetsPtr
  where
    bytes = assembleHost unit

installUnit :: PredKey -> Int -> Int -> JitUnit -> IO (Maybe JitKernel)
installUnit key arity cellsPerIter = installUnitAs key arity cellsPerIter (-1)

installUnitAs :: PredKey -> Int -> Int -> Int -> JitUnit -> IO (Maybe JitKernel)
installUnitAs key arity cellsPerIter scanPos unit
  | not jitEnabled = pure Nothing
  | otherwise = do
      let bytes = assembleHost unit
      if null bytes
        then pure Nothing
        else do
          ptr <- withArray bytes $ \pb -> c_inferaJitAlloc pb (fromIntegral (length bytes))
          if ptr == nullPtr
            then do
              jitDebug (show key ++ ": infera_jit_alloc failed")
              pure Nothing
            else do
              scratch <- mallocForeignPtrArray 24
              withForeignPtr scratch $ \sp -> do
                pokeElemOff sp scratchBailCapIdx (-1)
                pokeElemOff sp scratchBailHIdx (-1)
              let addr = fromIntegral (ptrToIntPtr ptr)
                  fnPtr = castPtrToFunPtr ptr
              jitDebug (show key ++ ": compiled (" ++ show (length bytes) ++ " bytes, " ++ arch ++ ")")
              pure (Just (JitKernel key arity fnPtr addr cellsPerIter scratch scanPos Nothing Nothing))

-- | Attempt to compile a predicate into a native 'JitKernel' at program load
-- time. Checks 2-level nested callers (@safe/1@, @nrev/2@) and then runs the
-- unified Horizon 1 + Horizon 4 general tail-recursive / TRMC compiler
-- ('compileGeneralTailJit').
compileJitKernel :: Symbols -> (String -> Int -> Bool) -> Word' -> Word' -> P.Program -> PredKey -> [P.Signature] -> P.Signature -> [S.Clause] -> IO (Maybe JitKernel)
compileJitKernel syms isBuiltin nilW consW prog key decls inferred clauses
  | not jitEnabled = pure Nothing
  | null decls,
    Just (pos, pattern) <- scanShape key clauses,
    Just p <- P.lookupPred key prog,
    not (P.predIsTabled prog p),
    not (P.nameHasFlag prog (fst key) S.FlagDynamic) = do
      jitDebug (show key ++ ": list search on argument " ++ show pos)
      installUnitAs key (snd key) 0 pos (compileScanKernel consW (snd key) pos pattern)
  | not (null decls) && any (\sig -> P.sigDet sig `notElem` [S.Det, S.Semidet]) decls = do
      jitDebug (show key ++ ": declined (non-det declared contract)")
      pure Nothing
  | P.sigDet inferred `elem` [S.Det, S.Semidet],
    Just (unit, cellsPerIter) <- matchSafeLoop nilW consW prog key clauses =
      installUnit key (snd key) cellsPerIter unit
  | P.sigDet inferred `elem` [S.Det, S.Semidet],
    Just (unit, cellsPerIter) <- matchNrevLoop nilW consW prog key clauses =
      installUnit key (snd key) cellsPerIter unit
  | Just (unit, cellsPerIter) <- compileGeneralTailJit nilW consW key inferred clauses =
      installUnit key (snd key) cellsPerIter unit
  | not clauseUnitsOn = do
      jitDebug (show key ++ ": declined (outside JIT fragment)")
      pure Nothing
  | Left why <- admitClauseUnit isBuiltin prog key = do
      jitDebug (show key ++ ": declined (outside JIT fragment; clause unit: " ++ why ++ ")")
      pure Nothing
  | otherwise = pure (Just (deferredUnit key (unsafePerformIO compile)))
  where
    -- Planning and assembly cost about 3M instructions a unit, so they
    -- wait for the predicate's first call.
    compile = do
      plan <- planClauseUnit syms isBuiltin prog key
      case plan of
        Left why -> do
          jitDebug (show key ++ ": declined (clause unit: " ++ why ++ ")")
          pure Nothing
        Right up -> installClauseUnit key up

-- | A clause unit compiled on first use; 'invokeJitKernel' forces it.
deferredUnit :: PredKey -> Maybe JitKernel -> JitKernel
deferredUnit key unit = JitKernel key (snd key) nullFunPtr 0 0 noScratch (-3) Nothing unit

noScratch :: ForeignPtr Int64
noScratch = unsafePerformIO (mallocForeignPtrArray 1)
{-# NOINLINE noScratch #-}

-- | @INFERA_JIT_CLAUSES=0@ turns off the clause compiler alone.
clauseUnitsOn :: Bool
clauseUnitsOn = unsafePerformIO (maybe True (/= "0") <$> lookupEnv "INFERA_JIT_CLAUSES")
{-# NOINLINE clauseUnitsOn #-}

-- Clause unit scratch: state (12 words), budgets (2), argument slots, then
-- the heap limit and entry heap top of the last capacity bailout.
cuStateWords, cuBudgetsAt, cuArgsAt :: Int
cuStateWords = 12
cuBudgetsAt = 12
cuArgsAt = 14

cuInitialStack, cuMaxStack :: Int
cuInitialStack = 4096
cuMaxStack = 1 `shiftL` 26

installClauseUnit :: PredKey -> UnitPlan -> IO (Maybe JitKernel)
installClauseUnit key up = do
  let bytes = assembleHost (upUnit up)
  if null bytes
    then pure Nothing
    else do
      ptr <- withArray bytes $ \pb -> c_inferaJitAlloc pb (fromIntegral (length bytes))
      if ptr == nullPtr
        then jitDebug (show key ++ ": infera_jit_alloc failed") >> pure Nothing
        else do
          let slots = upArgSlots up
          scratch <- mallocForeignPtrArray (cuArgsAt + slots + 3)
          withForeignPtr scratch $ \sp -> do
            pokeElemOff sp (cuArgsAt + slots) (-1)
            pokeElemOff sp (cuArgsAt + slots + 1) (-1)
            pokeElemOff sp (cuArgsAt + slots + 2) 0
          stack <- mallocForeignPtrArray cuInitialStack
          stackRef <- newIORef (stack, cuInitialStack)
          jitDebug (show key ++ ": clause unit of " ++ show (upPreds up) ++ " (" ++ show (length bytes) ++ " bytes, " ++ arch ++ ")")
          pure (Just (JitKernel key (snd key) (castPtrToFunPtr ptr) (fromIntegral (ptrToIntPtr ptr)) slots scratch (-2) (Just stackRef) Nothing))

-- ─── Horizon 1 + Horizon 4: General Tail-Recursive & TRMC JIT Compiler ───────

data ParamRole
  = ParamInt
  | ParamList
  | ParamOut
  | ParamOutList
  deriving (Eq, Show)

data VarKind
  = VKInt !Reg
  | VKList !Reg
  | VKWord !Reg
  deriving (Eq, Show)

isOutputRole :: ParamRole -> Bool
isOutputRole = \case
  ParamOut -> True
  ParamOutList -> True
  _ -> False

paramReg :: Int -> [ParamRole] -> Reg
paramReg idx roles
  | idx == length roles - 1 && isOutputRole (last roles) = RT3
  | otherwise = case idx of
      0 -> RT0
      1 -> RT1
      2 -> RT2
      _ -> RT3

initialFreeRegs :: [ParamRole] -> [Reg]
initialFreeRegs roles =
  let used = [paramReg i roles | i <- [0 .. length roles - 1]]
      pool = [RT0, RT1, RT2, RT3, RT4, RT5, RT6]
   in filter (`notElem` used) pool

compileGeneralTailJit :: Word' -> Word' -> PredKey -> P.Signature -> [S.Clause] -> Maybe (JitUnit, Int)
compileGeneralTailJit nilW consW (name, arity) inferred clauses
  | arity < 1 || arity > 4 || null clauses || length clauses > 8 = Nothing
  | not (any (isRecursiveClause name arity) clauses) = Nothing
  | not (all (hasValidHead name arity) clauses) = Nothing
  | not (all clauseLitsImmediate clauses) = Nothing
  | otherwise = do
      roles <- inferParamRoles name arity clauses
      let inCount = if isOutputRole (last roles) then arity - 1 else arity
          switchIdxs = P.sigSwitch inferred
          commitsOnSuccess = P.sigDet inferred == S.Semidet && all (< inCount) switchIdxs
      (reliesOnCommit, exclGroundIdxs) <- commitSafety name arity inCount roles commitsOnSuccess clauses
      let nilImm = fromIntegral nilW :: Int64
          consPlain = fromIntegral consW :: Int64
          consGround = fromIntegral (consW .|. groundBit) :: Int64
          -- When a matching base clause stands in for the interpreter's
          -- committed first answer, every input must be ground as the
          -- interpreter's switch check requires; integers already are.
          listIdxs = [i | (i, ParamList) <- zip [0 :: Int ..] roles]
          groundCheckIdxs =
            nub (trmcGroundPassthroughIdxs name arity roles clauses ++ [i | reliesOnCommit, i <- listIdxs] ++ exclGroundIdxs)
          prologue = emitEntryChecks roles groundCheckIdxs nilImm consGround
      clauseBlocks <-
        sequence
          [ compileClause nilImm consPlain consGround name roles idx ("clause_" ++ show (idx + 1)) cl
            | (idx, cl) <- zip [0 :: Int ..] clauses
          ]
      let failLbl = "clause_" ++ show (length clauses)
          cellsPerIter = if last roles == ParamOutList then 3 else 0
          epilogues =
            [ JLabel failLbl,
              JReturn jitFailure,
              JLabel "decline",
              JReturn jitDeclined,
              JLabel "bailout",
              JReturn jitBailout,
              JLabel "exhausted",
              JReturn jitExhausted
            ]
      pure (JitUnit (prologue ++ [JLabel "loop"] ++ concat clauseBlocks ++ epilogues), cellsPerIter)

hasValidHead :: String -> Int -> S.Clause -> Bool
hasValidHead name arity cl = case S.clauseHead cl of
  S.Compound hName args -> hName == name && length args == arity
  _ -> False

isRecursiveClause :: String -> Int -> S.Clause -> Bool
isRecursiveClause name arity cl = case reverse (S.clauseBody cl) of
  S.Compound rName rArgs : _ -> rName == name && length rArgs == arity
  _ -> False

inferParamRoles :: String -> Int -> [S.Clause] -> Maybe [ParamRole]
inferParamRoles name arity clauses = do
  let hasOutList = arity >= 2 && all (clauseSupportsOutListParam name arity) clauses && any (clauseEmitsCons name arity) clauses
      hasOutScalar = not hasOutList && arity >= 2 && all (clauseSupportsOutParam name arity) clauses
      hasOut = hasOutList || hasOutScalar
      inCount = if hasOut then arity - 1 else arity
      passthroughIdxs
        | not hasOutList = []
        | otherwise =
            [ idx
              | cl <- clauses,
                not (isRecursiveClause name arity cl),
                let S.Compound _ headArgs = S.clauseHead cl,
                S.Var outV <- [last headArgs],
                (idx, S.Var inV) <- zip [0 .. inCount - 1] (init headArgs),
                inV == outV
            ]
  inRoles <- mapM (inferInputRole passthroughIdxs clauses) [0 .. inCount - 1]
  let outRole
        | hasOutList = [ParamOutList]
        | hasOutScalar = [ParamOut]
        | otherwise = []
  pure (inRoles ++ outRole)

clauseSupportsOutListParam :: String -> Int -> S.Clause -> Bool
clauseSupportsOutListParam name arity cl =
  let headArgs = case S.clauseHead cl of
        S.Compound _ as -> as
        _ -> []
      lastHead = last headArgs
      initHeadVars = concatMap termVars (init headArgs)
      body = S.clauseBody cl
   in if isRecursiveClause name arity cl
        then case (lastHead, last body) of
          (S.Compound "cons" [elemPat, S.Var outTailV], S.Compound _ recArgs) ->
            last recArgs == S.Var outTailV
              && outTailV >= 0
              && outTailV `notElem` initHeadVars
              && outTailV `notElem` termVars elemPat
              && all (notElem outTailV . termVars) (init body)
              && all isGuardOrIs (init body)
              && isValidTrmcElem elemPat initHeadVars (init body)
          (S.Var outV, S.Compound _ recArgs) ->
            last recArgs == S.Var outV
              && outV >= 0
              && outV `notElem` initHeadVars
              && all (notElem outV . termVars) (init body)
              && all isGuardOrIs (init body)
          _ -> False
        else
          all isGuardOrIs body
            && case lastHead of
              S.Atom "nil" -> True
              S.Compound "cons" [elemPat, S.Atom "nil"] ->
                isValidTrmcElem elemPat initHeadVars body
              S.Var outV ->
                outV >= 0 && outV `elem` initHeadVars
              _ -> False

isValidTrmcElem :: S.Term -> [S.VarId] -> [S.Term] -> Bool
isValidTrmcElem elemPat initHeadVars goals = case elemPat of
  S.IntLit _ -> True
  S.Var v -> v >= 0 && (v `elem` initHeadVars || any (definesVarWithIs v) goals)
  _ -> False

clauseEmitsCons :: String -> Int -> S.Clause -> Bool
clauseEmitsCons name arity cl =
  let S.Compound _ headArgs = S.clauseHead cl
   in case last headArgs of
        S.Compound "cons" [_, _] -> True
        _ -> False
  where
    _ = (name, arity)

trmcGroundPassthroughIdxs :: String -> Int -> [ParamRole] -> [S.Clause] -> [Int]
trmcGroundPassthroughIdxs name arity roles clauses
  | last roles /= ParamOutList = []
  | otherwise =
      nub
        [ idx
          | cl <- clauses,
            not (isRecursiveClause name arity cl),
            let S.Compound _ headArgs = S.clauseHead cl,
            S.Var outV <- [last headArgs],
            (idx, S.Var inV) <- zip [0 .. arity - 2] (init headArgs),
            inV == outV
        ]

clauseSupportsOutParam :: String -> Int -> S.Clause -> Bool
clauseSupportsOutParam name arity cl =
  let headArgs = case S.clauseHead cl of
        S.Compound _ as -> as
        _ -> []
      lastHead = last headArgs
      initHeadVars = concatMap termVars (init headArgs)
      body = S.clauseBody cl
   in if isRecursiveClause name arity cl
        then case (lastHead, last body) of
          (S.Var outV, S.Compound _ recArgs) ->
            last recArgs == S.Var outV
              && outV >= 0
              && outV `notElem` initHeadVars
              && all (notElem outV . termVars) (init body)
          _ -> False
        else case lastHead of
          S.IntLit _ -> all isGuardOrIs body
          S.Var outV ->
            outV >= 0
              && all isGuardOrIs body
              && (outV `elem` initHeadVars || any (definesVarWithIs outV) body)
          _ -> False

isGuardOrIs :: S.Term -> Bool
isGuardOrIs = \case
  S.Compound "is" [S.Var _, _] -> True
  S.Compound "is" [S.IntLit _, _] -> True
  S.Compound op [_, _] -> isCmpOp op
  _ -> False

definesVarWithIs :: S.VarId -> S.Term -> Bool
definesVarWithIs v = \case
  S.Compound "is" [S.Var lhs, _] -> lhs == v
  _ -> False

inferInputRole :: [Int] -> [S.Clause] -> Int -> Maybe ParamRole
inferInputRole passthroughIdxs clauses idx =
  let pats = [as !! idx | cl <- clauses, S.Compound _ as <- [S.clauseHead cl]]
      usesList = idx `elem` passthroughIdxs || any isListPat pats
      usesInt = any isIntPat pats
   in if usesList && usesInt
        then Nothing
        else Just (if usesList then ParamList else ParamInt)
  where
    isListPat = \case
      S.Atom "nil" -> True
      S.Compound "cons" [_, _] -> True
      _ -> False
    isIntPat = \case
      S.IntLit _ -> True
      _ -> False

emitEntryChecks :: [ParamRole] -> [Int] -> Int64 -> Int64 -> [JitOp]
emitEntryChecks roles groundCheckIdxs nilImm consGround =
  [ JLoadImm RT0 RState stateClpIdx,
    JBranchImm JNe RT0 0 "decline"
  ]
    ++ concat [emitParamEntry i r | (i, r) <- zip [0 :: Int ..] roles]
  where
    emitParamEntry idx = \case
      ParamInt ->
        let reg = paramReg idx roles
         in [ JLoadImm reg RArgs idx,
              JDeref reg reg,
              JTagOf RT7 reg,
              JBranchImm JNe RT7 (fromIntegral tagInt) "decline",
              JValOf reg reg
            ]
      ParamList
        | idx `elem` groundCheckIdxs ->
            let reg = paramReg idx roles
                strCheckLbl = "entry_gnd_str_" ++ show idx
                okLbl = "entry_list_ok_" ++ show idx
             in [ JLoadImm reg RArgs idx,
                  JDeref reg reg,
                  JBranchImm JEq reg nilImm okLbl,
                  JTagOf RT7 reg,
                  JBranchImm JEq RT7 (fromIntegral tagStr) strCheckLbl,
                  JBranchImm JEq RT7 (fromIntegral tagRef) "decline",
                  JJump okLbl,
                  JLabel strCheckLbl,
                  JValOf RT7 reg,
                  JLoadIx RT7 RCells RT7,
                  JBranchImm JEq RT7 consGround okLbl,
                  JJump "decline",
                  JLabel okLbl
                ]
        | otherwise ->
            let reg = paramReg idx roles
                okLbl = "entry_list_ok_" ++ show idx
             in [ JLoadImm reg RArgs idx,
                  JDeref reg reg,
                  JBranchImm JEq reg nilImm okLbl,
                  JTagOf RT7 reg,
                  JBranchImm JNe RT7 (fromIntegral tagStr) "decline",
                  JLabel okLbl
                ]
      ParamOut ->
        let reg = paramReg idx roles
            okLbl = "entry_out_ok_" ++ show idx
         in [ JLoadImm reg RArgs idx,
              JDeref reg reg,
              JTagOf RT7 reg,
              JBranchImm JEq RT7 (fromIntegral tagRef) okLbl,
              JBranchImm JEq RT7 (fromIntegral tagInt) okLbl,
              JJump "decline",
              JLabel okLbl
            ]
      ParamOutList ->
        let reg = paramReg idx roles
         in [ JLoadImm reg RArgs idx,
              JDeref reg reg,
              JTagOf RT7 reg,
              JBranchImm JNe RT7 (fromIntegral tagRef) "decline",
              -- The occurs guard compares copied elements with this word.
              JStoreImm reg RArgs idx
            ]

-- ─── Commit safety ───────────────────────────────────────────────────────────

-- | Literals must fit an immediate integer; a wider one would be truncated.
clauseLitsImmediate :: S.Clause -> Bool
clauseLitsImmediate cl = all fits (concatMap termInts (S.clauseHead cl : S.clauseBody cl))
  where
    fits k = k >= -(2 ^ (60 :: Int)) && k < 2 ^ (60 :: Int)
    termInts = \case
      S.IntLit k -> [k]
      S.Compound _ as -> concatMap termInts as
      _ -> []

-- | Native code commits to the first clause whose head and guards match,
-- but the interpreter tries later clauses again if that clause fails in its
-- recursive call, and offers them as further answers after a base clause
-- succeeds. So a recursive clause must exclude every later clause outright.
-- A base clause may overlap later ones only when the interpreter commits on
-- success too: an inferred semidet predicate whose switch arguments are
-- input positions, ground at the call. Returns whether that is relied on.
--
-- A pair is exclusive by this module's own analysis ('clausesExclusive'),
-- or by determinism inference ('Infer.exclusive') when every argument it
-- needs ground is an input the entry checks make ground: integers already
-- are, and list arguments are returned for a ground check. Either way the
-- later clause must not raise an error the earlier one would not
-- ('laterRaisesNothingNew').
commitSafety :: String -> Int -> Int -> [ParamRole] -> Bool -> [S.Clause] -> Maybe (Bool, [Int])
commitSafety name arity inCount roles commitsOnSuccess clauses =
  foldM step (False, []) [(ci, cj) | (i, ci) <- indexed, (j, cj) <- indexed, i < j]
  where
    indexed = zip [0 :: Int ..] clauses
    step (acc, gnd) (ci, cj)
      -- Heads that cannot both match: the later clause's guards never run.
      | headsExclusive inCount ci cj = Just (acc, gnd)
      | laterRaisesNothingNew inCount ci cj,
        clausesExclusive inCount ci cj =
          Just (acc, gnd)
      | laterRaisesNothingNew inCount ci cj,
        Just ps <- I.exclusive ci cj,
        all groundable ps =
          Just (acc, nub (gnd ++ [p | p <- ps, roles !! p == ParamList]))
      | not (isRecursiveClause name arity ci) && commitsOnSuccess = Just (True, gnd)
      | otherwise = Nothing
    groundable p = p < inCount && roles !! p `elem` [ParamInt, ParamList]

-- ─── Per-clause compilation ──────────────────────────────────────────────────

type VarEnv = M.Map S.VarId VarKind

clauseVarCount :: S.VarId -> S.Clause -> Int
clauseVarCount v cl =
  length $ filter (== v) (concatMap termVars (S.clauseHead cl : S.clauseBody cl))

isAnonOrSingleton :: S.VarId -> S.Clause -> Bool
isAnonOrSingleton v cl = v < 0 || clauseVarCount v cl <= 1

clauseUsesVarAsInt :: S.VarId -> S.Clause -> Bool
clauseUsesVarAsInt v cl =
  any goalUsesAsInt (S.clauseBody cl)
  where
    goalUsesAsInt = \case
      S.Compound "is" [lhs, rhs] -> v `elem` termVars lhs || v `elem` termVars rhs
      S.Compound op [a, b] | isCmpOp op -> v `elem` termVars a || v `elem` termVars b
      _ -> False

compileClause ::
  Int64 ->
  Int64 ->
  Int64 ->
  String ->
  [ParamRole] ->
  Int ->
  Label ->
  S.Clause ->
  Maybe [JitOp]
compileClause nilImm consPlain consGround predName roles clauseIdx nextLbl cl = do
  let S.Compound _ headArgs = S.clauseHead cl
      body = S.clauseBody cl
      lastRole = last roles
      hasOut = isOutputRole lastRole
      inCount = if hasOut then length roles - 1 else length roles
      free0 = initialFreeRegs roles
  (headOps, env1, free1) <-
    compileHeadArgs nilImm consPlain consGround cl roles clauseIdx nextLbl 0 inCount headArgs M.empty free0
  let freeAfterHead = recycleDeadVars (body ++ [last headArgs | hasOut]) env1 free1
  if isRecursiveClause predName (length roles) cl
    then do
      let guardAndIsGoals = init body
          S.Compound _ recArgs = last body
          recInArgs = if hasOut then init recArgs else recArgs
          extraLive = [last headArgs | lastRole == ParamOutList]
      (bodyOps, env2, free2) <-
        compileBodyGoals nextLbl guardAndIsGoals (recInArgs ++ extraLive) env1 freeAfterHead
      trmcStepOps <-
        if lastRole == ParamOutList
          then compileTrmcStepOutput consPlain consGround (show clauseIdx) (length roles - 1) (last headArgs) env2
          else Just []
      let free3 = recycleDeadVars recInArgs env2 free2
      moveOps <- compileTailCallMoves roles recInArgs env2 free3
      pure
        ( [JLabel ("clause_" ++ show clauseIdx)]
            ++ headOps
            ++ bodyOps
            ++ trmcStepOps
            ++ moveOps
            -- A last call keeps its caller's continuation depth: no tick.
            ++ [JJump "loop"]
        )
    else do
      let outHeads = [last headArgs | hasOut]
      (bodyOps, env2, _free2) <-
        compileBodyGoals nextLbl body outHeads env1 freeAfterHead
      retOps <- case lastRole of
        ParamOut -> compileBaseOutput clauseIdx nextLbl (last headArgs) env2
        ParamOutList -> compileTrmcBaseOutput nilImm consPlain consGround (show clauseIdx) (length roles - 1) (last headArgs) env2
        _ -> Just [JReturn jitSuccess]
      pure
        ( [JLabel ("clause_" ++ show clauseIdx)]
            ++ headOps
            ++ bodyOps
            ++ retOps
        )

compileHeadArgs ::
  Int64 ->
  Int64 ->
  Int64 ->
  S.Clause ->
  [ParamRole] ->
  Int ->
  Label ->
  Int ->
  Int ->
  [S.Term] ->
  VarEnv ->
  [Reg] ->
  Maybe ([JitOp], VarEnv, [Reg])
compileHeadArgs nilImm consPlain consGround cl roles clauseIdx nextLbl idx limit args env freeRegs
  | idx >= limit = Just ([], env, freeRegs)
  | otherwise = do
      let pat = args !! idx
          role = roles !! idx
          pReg = paramReg idx roles
      (ops1, env1, free1) <-
        compileHeadPat nilImm consPlain consGround cl clauseIdx idx nextLbl role pReg pat env freeRegs
      (ops2, env2, free2) <-
        compileHeadArgs nilImm consPlain consGround cl roles clauseIdx nextLbl (idx + 1) limit args env1 free1
      pure (ops1 ++ ops2, env2, free2)

compileHeadPat ::
  Int64 ->
  Int64 ->
  Int64 ->
  S.Clause ->
  Int ->
  Int ->
  Label ->
  ParamRole ->
  Reg ->
  S.Term ->
  VarEnv ->
  [Reg] ->
  Maybe ([JitOp], VarEnv, [Reg])
compileHeadPat nilImm consPlain consGround cl clauseIdx argIdx nextLbl role pReg pat env freeRegs =
  case (role, pat) of
    (_, S.Var v) | v < 0 -> Just ([], env, freeRegs)
    (ParamInt, S.IntLit v) ->
      Just ([JBranchImm JNe pReg (fromIntegral v) nextLbl], env, freeRegs)
    (ParamInt, S.Var v) ->
      case M.lookup v env of
        Nothing -> Just ([], M.insert v (VKInt pReg) env, freeRegs)
        Just (VKInt prevReg) ->
          Just ([JBranchCmp JNe pReg prevReg nextLbl], env, freeRegs)
        Just _ -> Nothing
    (ParamList, S.Atom "nil") ->
      Just (nilCheckOps ("nil_" ++ tag) nextLbl pReg nilImm, env, freeRegs)
    (ParamList, S.Var v) ->
      case M.lookup v env of
        Nothing -> Just ([], M.insert v (VKList pReg) env, freeRegs)
        Just (VKList prevReg) ->
          Just (sameWordOps ("leq_" ++ tag) nextLbl pReg prevReg, env, freeRegs)
        Just _ -> Nothing
    (ParamList, S.Compound "cons" [hPat, tPat]) -> do
      let consOkLbl = "head_cons_ok_" ++ tag
      let unpackPrefix =
            [ -- [] never matches [_ | _]; anything but a structure (an
              -- unbound tail above all) goes back to the interpreter.
              JBranchImm JEq pReg nilImm nextLbl,
              JTagOf RT7 pReg,
              JBranchImm JNe RT7 (fromIntegral tagStr) "bailout",
              JValOf RT7 pReg
            ]
      (tmpReg, _) <- unconsReg freeRegs
      let funCheck =
            [ JLoadIx tmpReg RCells RT7,
              JBranchImm JEq tmpReg consPlain consOkLbl,
              JBranchImm JEq tmpReg consGround consOkLbl,
              JJump "bailout",
              JLabel consOkLbl
            ]
      (subOps, env', free') <- compileConsSubpats nilImm cl tag nextLbl hPat tPat env freeRegs
      pure (unpackPrefix ++ funCheck ++ subOps, env', free')
    _ -> Nothing
  where
    tag = show clauseIdx ++ "_" ++ show argIdx

-- | Match the head and tail of the cons cell at RT7. Both are loaded before
-- any check, since the checks use RT7 as scratch. A check jumps to the next
-- clause only on a definite mismatch between bound values; an unbound value,
-- a compound or a boxed number goes to the interpreter instead.
compileConsSubpats ::
  Int64 ->
  S.Clause ->
  String ->
  Label ->
  S.Term ->
  S.Term ->
  VarEnv ->
  [Reg] ->
  Maybe ([JitOp], VarEnv, [Reg])
compileConsSubpats nilImm cl tag nextLbl hPat tPat env free0 = do
  let anon = \case
        S.Var v -> isAnonOrSingleton v cl
        _ -> False
      needT = not (anon tPat)
      needH = not (anon hPat)
  (rT, free1) <- if needT then unconsReg free0 else Just (RT7, free0)
  (rH, free2) <- if needH then unconsReg free1 else Just (RT7, free1)
  let loads =
        [op | needT, op <- [JAddImm rT RT7 2, JLoadIx rT RCells rT, JDeref rT rT]]
          ++ [op | needH, op <- [JAddImm rH RT7 1, JLoadIx rH RCells rH, JDeref rH rH]]
  (tOps, env1, keepT) <-
    if not needT
      then Just ([], env, False)
      else case tPat of
        S.Atom "nil" -> Just (nilCheckOps ("tnil_" ++ tag) nextLbl rT nilImm, env, False)
        S.Var tv -> case M.lookup tv env of
          Nothing -> Just ([], M.insert tv (VKList rT) env, True)
          Just (VKList prevReg) -> Just (sameWordOps ("teq_" ++ tag) nextLbl rT prevReg, env, False)
          Just _ -> Nothing
        _ -> Nothing
  (hOps, env2, keepH) <-
    if not needH
      then Just ([], env1, False)
      else case hPat of
        S.IntLit k -> Just (intLitWordOps ("hlit_" ++ tag) nextLbl rH k, env1, False)
        S.Var hv -> case M.lookup hv env1 of
          Nothing
            | clauseUsesVarAsInt hv cl -> Just (intCheckOps rH, M.insert hv (VKInt rH) env1, True)
            | otherwise -> Just ([], M.insert hv (VKWord rH) env1, True)
          Just (VKInt prevReg) ->
            Just (intCheckOps rH ++ [JBranchCmp JNe rH prevReg nextLbl], env1, False)
          Just (VKWord prevReg) -> Just (sameWordOps ("heq_" ++ tag) nextLbl rH prevReg, env1, False)
          Just _ -> Nothing
        _ -> Nothing
  let free3 = free2 ++ [rT | needT, not keepT] ++ [rH | needH, not keepH]
  pure (loads ++ tOps ++ hOps, env2, free3)

-- | Jump to @target@ when @r@ holds an immediate constant (RT7 keeps the tag).
constTagOps :: Reg -> Label -> [JitOp]
constTagOps r target =
  [ JTagOf RT7 r,
    JBranchImm JEq RT7 (fromIntegral tagInt) target,
    JBranchImm JEq RT7 (fromIntegral tagAtm) target,
    JBranchImm JEq RT7 (fromIntegral tagChr) target
  ]

-- | A repeated variable: equal words unify, two different constants do not,
-- and anything else is decided by the interpreter's unification.
sameWordOps :: String -> Label -> Reg -> Reg -> [JitOp]
sameWordOps lbl nextLbl a b =
  [JBranchCmp JEq a b okLbl]
    ++ constTagOps a constLbl
    ++ [JJump "bailout", JLabel constLbl]
    ++ constTagOps b nextLbl
    ++ [JJump "bailout", JLabel okLbl]
  where
    okLbl = lbl ++ "_ok"
    constLbl = lbl ++ "_const"

-- | @[]@ against a word: an unbound word could still become @[]@.
nilCheckOps :: String -> Label -> Reg -> Int64 -> [JitOp]
nilCheckOps lbl nextLbl r nilImm =
  [ JBranchImm JEq r nilImm okLbl,
    JTagOf RT7 r,
    JBranchImm JEq RT7 (fromIntegral tagRef) "bailout",
    JJump nextLbl,
    JLabel okLbl
  ]
  where
    okLbl = lbl ++ "_ok"

-- | An integer literal against a word: a different constant is a mismatch,
-- a boxed number or an unbound word is not decided here.
intLitWordOps :: String -> Label -> Reg -> Integer -> [JitOp]
intLitWordOps lbl nextLbl r k =
  [JBranchImm JEq r (fromIntegral (intWord (fromIntegral k))) okLbl]
    ++ constTagOps r nextLbl
    ++ [JJump "bailout", JLabel okLbl]
  where
    okLbl = lbl ++ "_ok"

-- | Unbox an integer element; anything else goes to the interpreter.
intCheckOps :: Reg -> [JitOp]
intCheckOps r =
  [ JTagOf RT7 r,
    JBranchImm JNe RT7 (fromIntegral tagInt) "bailout",
    JValOf r r
  ]

-- ─── Body goals (comparisons and `is` assignments) with liveness recycling ──

compileBodyGoals ::
  Label ->
  [S.Term] ->
  [S.Term] ->
  VarEnv ->
  [Reg] ->
  Maybe ([JitOp], VarEnv, [Reg])
compileBodyGoals _ [] _ env freeRegs = Just ([], env, freeRegs)
compileBodyGoals nextLbl (g : gs) tailTerms env freeRegs = do
  (ops1, env1, free1) <- compileOneGoal nextLbl g env freeRegs
  let free1' = recycleDeadVars (gs ++ tailTerms) env1 free1
  (ops2, env2, free2) <- compileBodyGoals nextLbl gs tailTerms env1 free1'
  pure (ops1 ++ ops2, env2, free2)

compileOneGoal :: Label -> S.Term -> VarEnv -> [Reg] -> Maybe ([JitOp], VarEnv, [Reg])
compileOneGoal nextLbl goal env freeRegs = case goal of
  S.Compound "is" [S.Var lhs, expr] | lhs >= 0 -> do
    case M.lookup lhs env of
      Nothing -> do
        (dstReg, free') <- unconsReg freeRegs
        ops <- compileArithExpr dstReg expr env free'
        pure (ops, M.insert lhs (VKInt dstReg) env, free')
      Just (VKInt existingReg) -> do
        ops <- compileArithExpr RT7 expr env freeRegs
        pure (ops ++ [JBranchCmp JNe existingReg RT7 nextLbl], env, freeRegs)
      Just _ -> Nothing
  -- `k is E` evaluates E and compares it with the literal: both integers
  -- here, so identity is equality.
  S.Compound "is" [S.IntLit k, expr] -> do
    ops <- compileArithExpr RT7 expr env freeRegs
    pure (ops ++ [JBranchImm JNe RT7 (fromIntegral k) nextLbl], env, freeRegs)
  -- != is structural: 3 + 1 != 4 holds. It is an integer test only when
  -- both sides are integers already.
  S.Compound "neq" [lhs, rhs] -> do
    let operand = \case
          S.Var v | Just (VKInt r) <- M.lookup v env -> Just (Left r)
          S.IntLit k -> Just (Right k)
          _ -> Nothing
    l <- operand lhs
    r <- operand rhs
    let ops = case (l, r) of
          (Left rl, Left rr) -> [JBranchCmp JEq rl rr nextLbl]
          (Left rl, Right k) -> [JBranchImm JEq rl (fromIntegral k) nextLbl]
          (Right k, Left rr) -> [JBranchImm JEq rr (fromIntegral k) nextLbl]
          (Right a, Right b) -> [JJump nextLbl | a == b]
    Just (ops, env, freeRegs)
  S.Compound op [lhs, rhs] | isCmpOp op -> do
    negCond <- negatedCmpCond op
    case (lhs, rhs) of
      (S.Var v, S.IntLit k)
        | Just (VKInt rL) <- M.lookup v env ->
            Just ([JBranchImm negCond rL (fromIntegral k) nextLbl], env, freeRegs)
      (S.Var v1, S.Var v2)
        | Just (VKInt r1) <- M.lookup v1 env,
          Just (VKInt r2) <- M.lookup v2 env ->
            Just ([JBranchCmp negCond r1 r2 nextLbl], env, freeRegs)
      _ -> do
        (rL, free1) <- unconsReg freeRegs
        opsL <- compileArithExpr rL lhs env free1
        opsR <- compileArithExpr RT7 rhs env free1
        pure (opsL ++ opsR ++ [JBranchCmp negCond rL RT7 nextLbl], env, freeRegs)
  _ -> Nothing


-- | The branch taken when an arithmetic comparison fails.
negatedCmpCond :: String -> Maybe Cond
negatedCmpCond = \case
  "lt" -> Just JGe
  "lte" -> Just JGt
  "gt" -> Just JLe
  "gte" -> Just JLt
  _ -> Nothing

compileArithExpr :: Reg -> S.Term -> VarEnv -> [Reg] -> Maybe [JitOp]
compileArithExpr dst expr env freeRegs = case expr of
  S.IntLit k -> Just [JMovImm dst (fromIntegral k)]
  S.Var v -> case M.lookup v env of
    Just (VKInt r) -> Just [JMov dst r | dst /= r]
    _ -> Nothing
  S.Compound op [a, b]
    | op `elem` ["plus", "minus", "mul", "mod"] -> do
        let comb rA rB = case op of
              "plus" -> JAddChecked dst rA rB "bailout"
              "minus" -> JSubChecked dst rA rB "bailout"
              "mod" -> JModChecked dst rA rB "bailout"
              _ -> JMulChecked dst rA rB "bailout"
        case (a, b) of
          (S.Var va, S.Var vb)
            | Just (VKInt ra) <- M.lookup va env,
              Just (VKInt rb) <- M.lookup vb env ->
                Just [comb ra rb]
          (S.Var va, S.IntLit kb)
            | Just (VKInt ra) <- M.lookup va env ->
                Just [JMovImm RT7 (fromIntegral kb), comb ra RT7]
          (S.IntLit ka, S.Var vb)
            | Just (VKInt rb) <- M.lookup vb env ->
                Just [JMovImm RT7 (fromIntegral ka), comb RT7 rb]
          _ -> do
            opsA <- compileArithExpr dst a env freeRegs
            (tmpB, free') <- if dst == RT7 then unconsReg freeRegs else Just (RT7, freeRegs)
            opsB <- compileArithExpr tmpB b env free'
            pure (opsA ++ opsB ++ [comb dst tmpB])
  _ -> Nothing

-- ─── Horizon 4: TRMC step and base output lowering ───────────────────────────

-- | Load an output element into RT7, with a guard run first. Unification
-- has an occurs check, so a copied element that could contain the output
-- variable (the variable itself, or a compound not known to be ground) goes
-- to the interpreter. The entry checks left the output word in args.
compileTaggedElemIntoRT7 :: Int64 -> String -> Int -> S.Term -> VarEnv -> Maybe ([JitOp], [JitOp])
compileTaggedElemIntoRT7 consGround lbl outIdx elemPat env = case elemPat of
  S.IntLit k ->
    Just ([], [JMovImm RT7 (fromIntegral (intWord (fromIntegral k)))])
  S.Var v -> case M.lookup v env of
    Just (VKInt r) -> Just ([], [JMkWord RT7 r tagInt])
    Just (VKWord r) -> Just (occursGuardOps consGround lbl outIdx r, [JMov RT7 r])
    Just (VKList r) -> Just (occursGuardOps consGround lbl outIdx r, [JMov RT7 r])
    Nothing -> Nothing
  _ -> Nothing

-- | Whether an element is an integer, so a cell holding it is ground.
elemIsGround :: S.Term -> VarEnv -> Bool
elemIsGround elemPat env = case elemPat of
  S.IntLit _ -> True
  S.Var v | Just (VKInt _) <- M.lookup v env -> True
  _ -> False

occursGuardOps :: Int64 -> String -> Int -> Reg -> [JitOp]
occursGuardOps consGround lbl outIdx r =
  constTagOps r okLbl
    ++ [ JBranchImm JEq RT7 (fromIntegral tagBox) okLbl,
         JBranchImm JEq RT7 (fromIntegral tagRef) refLbl,
         JBranchImm JNe RT7 (fromIntegral tagStr) "bailout",
         JValOf RT7 r,
         JLoadIx RT7 RCells RT7,
         JBranchImm JEq RT7 consGround okLbl,
         JJump "bailout",
         JLabel refLbl,
         JLoadImm RT7 RArgs outIdx,
         JBranchCmp JEq RT7 r "bailout",
         JLabel okLbl
       ]
  where
    okLbl = "occ_ok_" ++ lbl
    refLbl = "occ_ref_" ++ lbl

compileTrmcStepOutput :: Int64 -> Int64 -> String -> Int -> S.Term -> VarEnv -> Maybe [JitOp]
compileTrmcStepOutput consPlain consGround lbl outIdx outHeadPat env = case outHeadPat of
  S.Var _ -> Just []
  S.Compound "cons" [elemPat, S.Var _] -> do
    (guardOps, elemOps) <- compileTaggedElemIntoRT7 consGround lbl outIdx elemPat env
    Just
      ( guardOps
          ++ [ JLoadImm RT7 RState stateCapIdx,
               JAddImm RH RH 4,
               JBranchCmp JGt RH RT7 "bailout",
               JSubImm RH RH 4,
               JMovImm RT7 consPlain,
               JStoreIx RT7 RCells RH
             ]
          ++ elemOps
          ++ [ JAddImm RH RH 1,
               JStoreIx RT7 RCells RH,
               JSubImm RH RH 1,
               JMkWord RT7 RH tagStr,
               JValOf RT3 RT3,
               JBindRef RT3 RT7 "bailout",
               JAddImm RH RH 2,
               JMkWord RT3 RH tagRef,
               JStoreIx RT3 RCells RH,
               JAddImm RH RH 1
             ]
      )
  _ -> Nothing

compileTrmcBaseOutput :: Int64 -> Int64 -> Int64 -> String -> Int -> S.Term -> VarEnv -> Maybe [JitOp]
compileTrmcBaseOutput nilImm consPlain consGround lbl outIdx outHeadPat env = case outHeadPat of
  S.Atom "nil" ->
    Just
      [ JMovImm RT7 nilImm,
        JValOf RT3 RT3,
        JBindRef RT3 RT7 "bailout",
        JReturn jitSuccess
      ]
  S.Var v -> case M.lookup v env of
    Just (VKList r) ->
      Just
        ( occursGuardOps consGround lbl outIdx r
            ++ [ JValOf RT3 RT3,
                 JBindRef RT3 r "bailout",
                 JReturn jitSuccess
               ]
        )
    _ -> Nothing
  S.Compound "cons" [elemPat, S.Atom "nil"] -> do
    (guardOps, elemOps) <- compileTaggedElemIntoRT7 consGround lbl outIdx elemPat env
    let header = if elemIsGround elemPat env then consGround else consPlain
    Just
      ( guardOps
          ++ [ JLoadImm RT7 RState stateCapIdx,
               JAddImm RH RH 4,
               JBranchCmp JGt RH RT7 "bailout",
               JSubImm RH RH 4,
               JMovImm RT7 header,
               JStoreIx RT7 RCells RH
             ]
          ++ elemOps
          ++ [ JAddImm RH RH 1,
               JStoreIx RT7 RCells RH,
               JAddImm RH RH 1,
               JMovImm RT7 nilImm,
               JStoreIx RT7 RCells RH,
               JSubImm RH RH 2,
               JMkWord RT7 RH tagStr,
               JAddImm RH RH 3,
               JValOf RT3 RT3,
               JBindRef RT3 RT7 "bailout",
               JReturn jitSuccess
             ]
      )
  _ -> Nothing

-- ─── Tail-call parallel move emission & scalar base-clause output binding ────

compileTailCallMoves :: [ParamRole] -> [S.Term] -> VarEnv -> [Reg] -> Maybe [JitOp]
compileTailCallMoves roles recInArgs env freeRegs = do
  (prepOps, srcRegs, _) <-
    foldM
      ( \(accOps, accRegs, fr) (idx, argTerm) ->
          let dst = paramReg idx roles
           in case (roles !! idx, argTerm) of
                (ParamInt, S.Var v)
                  | Just (VKInt r) <- M.lookup v env ->
                      Just (accOps, accRegs ++ [(dst, r)], fr)
                (ParamList, S.Var v)
                  | Just (VKList r) <- M.lookup v env ->
                      Just (accOps, accRegs ++ [(dst, r)], fr)
                (ParamInt, _) -> do
                  (tmpR, fr') <- unconsReg fr
                  ops <- compileArithExpr tmpR argTerm env fr'
                  pure (accOps ++ ops, accRegs ++ [(dst, tmpR)], fr')
                _ -> Nothing
      )
      ([], [], freeRegs)
      (zip [0 :: Int ..] recInArgs)
  pure (prepOps ++ emitParallelMoves RT7 srcRegs)

emitParallelMoves :: Reg -> [(Reg, Reg)] -> [JitOp]
emitParallelMoves scratchReg pairs0 = go (filter (uncurry (/=)) pairs0)
  where
    go [] = []
    go pairs =
      let srcs = map snd pairs
       in case break (\(d, _) -> d `notElem` srcs) pairs of
            (pre, (d, s) : post) ->
              JMov d s : go (pre ++ post)
            (_, []) ->
              case pairs of
                (d, s) : rest ->
                  JMov scratchReg s
                    : go ((d, scratchReg) : map (\(d', s') -> (d', if s' == s then scratchReg else s')) rest)
                [] -> []

compileBaseOutput :: Int -> Label -> S.Term -> VarEnv -> Maybe [JitOp]
compileBaseOutput clauseIdx nextLbl outPat env = do
  (valOps, valReg) <- case outPat of
    S.IntLit k -> Just ([JMovImm RT4 (fromIntegral k)], RT4)
    S.Var v -> case M.lookup v env of
      Just (VKInt r) -> Just ([], r)
      _ -> Nothing
    _ -> Nothing
  let checkModeLbl = "base_out_check_" ++ show clauseIdx
  pure
    ( valOps
        ++ [ JTagOf RT7 RT3,
             JBranchImm JNe RT7 (fromIntegral tagRef) checkModeLbl,
             JMkWord RT7 valReg tagInt,
             JValOf RT3 RT3,
             JBindRef RT3 RT7 "bailout",
             JReturn jitSuccess,
             JLabel checkModeLbl,
             JValOf RT7 RT3,
             JBranchCmp JNe RT7 valReg nextLbl,
             JReturn jitSuccess
           ]
    )

-- ─── Liveness-based register recycling ───────────────────────────────────────

termVars :: S.Term -> [S.VarId]
termVars = \case
  S.Var v | v >= 0 -> [v]
  S.Compound _ as -> concatMap termVars as
  _ -> []

recycleDeadVars :: [S.Term] -> VarEnv -> [Reg] -> [Reg]
recycleDeadVars remainingTerms env freeRegs =
  let liveVars = Set.fromList (concatMap termVars remainingTerms)
      paramRegs = [RT0, RT1, RT2, RT3]
      -- Dead variables stay in the environment, so a register freed once
      -- and handed to a live variable must not be freed again through them.
      liveRegs = [regOf vk | (v, vk) <- M.toList env, v `Set.member` liveVars]
      deadRegs =
        [ regOf vk
          | (v, vk) <- M.toList env,
            v `Set.notMember` liveVars,
            regOf vk `notElem` paramRegs,
            regOf vk `notElem` liveRegs
        ]
   in nub (filter (`notElem` liveRegs) freeRegs ++ deadRegs)
  where
    regOf (VKInt r) = r
    regOf (VKList r) = r
    regOf (VKWord r) = r

unconsReg :: [Reg] -> Maybe (Reg, [Reg])
unconsReg [] = Nothing
unconsReg (r : rs) = Just (r, rs)

-- ─── 2-Level Nested List Callers (Track 2: safe/1 and nrev/2) ────────────────

matchSafeLoop :: Word' -> Word' -> P.Program -> PredKey -> [S.Clause] -> Maybe (JitUnit, Int)
matchSafeLoop nilW consW prog (name, 1) [cBase, cStep]
  | S.Compound bName [S.Atom "nil"] <- S.clauseHead cBase,
    bName == name && null (S.clauseBody cBase),
    S.Compound sName [S.Compound "cons" [S.Var vQ, S.Var vQs]] <- S.clauseHead cStep,
    sName == name,
    [ S.Compound helperName [S.Var vQ1, S.Var vQs1, S.IntLit initD],
      S.Compound rName [S.Var vQs2]
      ] <- S.clauseBody cStep,
    rName == name && vQ == vQ1 && vQs == vQs1 && vQs == vQs2 && initD > 0,
    helperDefinedAs isNoattDef prog (helperName, 3) =
      let consGround = fromIntegral (consW .|. groundBit) :: Int64
          consPlain = fromIntegral consW :: Int64
          nilImm = fromIntegral nilW :: Int64
       in Just
            ( JitUnit
                [ JLoadImm RT0 RState stateClpIdx,
                  JBranchImm JNe RT0 0 "decline",
                  JLoadImm RT0 RArgs 0,
                  JDeref RT0 RT0,
                  JBranchImm JEq RT0 nilImm "success",
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "decline",
                  JLabel "outer_loop",
                  JBranchImm JEq RT0 nilImm "success",
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "bailout",
                  JValOf RT3 RT0,
                  JLoadIx RT4 RCells RT3,
                  JBranchImm JEq RT4 consPlain "outer_cons_ok",
                  JBranchImm JEq RT4 consGround "outer_cons_ok",
                  JJump "bailout",
                  JLabel "outer_cons_ok",
                  JAddImm RT4 RT3 1,
                  JLoadIx RT1 RCells RT4,
                  JDeref RT1 RT1,
                  JTagOf RT5 RT1,
                  JBranchImm JNe RT5 (fromIntegral tagInt) "bailout",
                  JValOf RT1 RT1,
                  JAddImm RT4 RT3 2,
                  JLoadIx RT0 RCells RT4,
                  JDeref RT0 RT0,
                  -- Call noatt Q Qs initD (depth + 1; invokeJitKernel guarantees
                  -- one level of headroom), then its last calls: no ticks.
                  JMov RT2 RT0,
                  JMovImm RT6 (fromIntegral initD),
                  JLabel "inner_loop",
                  JBranchImm JEq RT2 nilImm "inner_done",
                  JTagOf RT3 RT2,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "bailout",
                  JValOf RT3 RT2,
                  JLoadIx RT4 RCells RT3,
                  JBranchImm JEq RT4 consPlain "inner_cons_ok",
                  JBranchImm JEq RT4 consGround "inner_cons_ok",
                  JJump "bailout",
                  JLabel "inner_cons_ok",
                  JAddImm RT4 RT3 1,
                  JLoadIx RT4 RCells RT4,
                  JDeref RT4 RT4,
                  JTagOf RT5 RT4,
                  JBranchImm JNe RT5 (fromIntegral tagInt) "bailout",
                  JValOf RT4 RT4,
                  JBranchCmp JEq RT1 RT4 "fail",
                  JSubChecked RT5 RT4 RT1 "bailout",
                  JBranchCmp JEq RT5 RT6 "fail",
                  JSubChecked RT5 RT1 RT4 "bailout",
                  JBranchCmp JEq RT5 RT6 "fail",
                  JAddImm RT5 RT3 2,
                  JLoadIx RT2 RCells RT5,
                  JDeref RT2 RT2,
                  JAddImm RT6 RT6 1,
                  JJump "inner_loop",
                  JLabel "inner_done",
                  -- Tail call safe Qs: a last call keeps its caller's depth
                  JJump "outer_loop",
                  JLabel "success",
                  JReturn jitSuccess,
                  JLabel "fail",
                  JReturn jitFailure,
                  JLabel "decline",
                  JReturn jitDeclined,
                  JLabel "bailout",
                  JReturn jitBailout,
                  JLabel "exhausted",
                  JReturn jitExhausted
                ],
              0
            )
matchSafeLoop _ _ _ _ _ = Nothing

matchNrevLoop :: Word' -> Word' -> P.Program -> PredKey -> [S.Clause] -> Maybe (JitUnit, Int)
matchNrevLoop nilW consW prog (name, 2) [cBase, cStep]
  | S.Compound bName [S.Atom "nil", S.Atom "nil"] <- S.clauseHead cBase,
    bName == name && null (S.clauseBody cBase),
    S.Compound sName [S.Compound "cons" [S.Var vH, S.Var vT], S.Var vR] <- S.clauseHead cStep,
    sName == name,
    [ S.Compound rName [S.Var vT1, S.Var vR1],
      S.Compound appName [S.Var vR1a, S.Compound "cons" [S.Var vH1, S.Atom "nil"], S.Var vR2]
      ] <- S.clauseBody cStep,
    rName == name && vT == vT1 && vR1 == vR1a && vH == vH1 && vR == vR2,
    helperDefinedAs isAppendDef prog (appName, 3) =
      let consGround = fromIntegral (consW .|. groundBit) :: Int64
          consPlain = fromIntegral consW :: Int64
          nilImm = fromIntegral nilW :: Int64
       in Just
            ( JitUnit
                [ JLoadImm RT0 RState stateClpIdx,
                  JBranchImm JNe RT0 0 "decline",
                  JLoadImm RT0 RArgs 0,
                  JDeref RT0 RT0,
                  JLoadImm RT2 RArgs 1,
                  JDeref RT2 RT2,
                  JTagOf RT3 RT2,
                  JBranchImm JNe RT3 (fromIntegral tagRef) "decline",
                  JMovImm RT1 nilImm,
                  JBranchImm JEq RT0 nilImm "base_case",
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "decline",
                  JMovImm RT6 2,
                  JLabel "loop",
                  JBranchImm JEq RT0 nilImm "base_case",
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "bailout",
                  JValOf RT3 RT0,
                  JLoadIx RT4 RCells RT3,
                  JBranchImm JEq RT4 consPlain "cons_ok",
                  JBranchImm JEq RT4 consGround "cons_ok",
                  JJump "bailout",
                  JLabel "cons_ok",
                  JLoadImm RT4 RState stateCapIdx,
                  JAddImm RT5 RH 4,
                  JBranchCmp JGt RT5 RT4 "bailout",
                  JAddImm RT4 RT3 1,
                  JLoadIx RT4 RCells RT4,
                  JDeref RT4 RT4,
                  -- Only constants are copied: a variable or compound element
                  -- could hold the output and need the occurs check.
                  JTagOf RT5 RT4,
                  JBranchImm JEq RT5 (fromIntegral tagInt) "head_ok",
                  JBranchImm JEq RT5 (fromIntegral tagAtm) "head_ok",
                  JBranchImm JEq RT5 (fromIntegral tagChr) "head_ok",
                  JJump "bailout",
                  JLabel "head_ok",
                  JAddImm RT5 RT3 2,
                  JLoadIx RT5 RCells RT5,
                  JDeref RT5 RT5,
                  JMovImm RT3 consPlain,
                  JStoreIx RT3 RCells RH,
                  JAddImm RT3 RH 1,
                  JStoreIx RT4 RCells RT3,
                  JAddImm RT3 RH 2,
                  JStoreIx RT1 RCells RT3,
                  JMkWord RT1 RH tagStr,
                  JAddImm RH RH 3,
                  JMov RT0 RT5,
                  -- One nested (non-last) nrev call per element
                  JTickDepth "exhausted",
                  JAddImm RT6 RT6 1,
                  JJump "loop",
                  JLabel "base_case",
                  JValOf RT2 RT2,
                  JBindRef RT2 RT1 "bailout",
                  JReturn jitSuccess,
                  JLabel "decline",
                  JReturn jitDeclined,
                  JLabel "bailout",
                  JReturn jitBailout,
                  JLabel "exhausted",
                  JReturn jitExhausted
                ],
              3
            )
matchNrevLoop _ _ _ _ _ = Nothing

-- | The fused safe/nrev kernels inline their helper's meaning, so they only
-- apply when the program defines the helper with exactly that meaning:
-- deterministic, and clauses of the expected shape.
helperDefinedAs :: (PredKey -> [S.Clause] -> Bool) -> P.Program -> PredKey -> Bool
helperDefinedAs shapeOk prog key = case P.lookupPred key prog of
  Just helper ->
    let decls = P.predDecls helper
     in (null decls || all (\sig -> P.sigDet sig `elem` [S.Det, S.Semidet]) decls)
          && P.sigDet (P.predInferred helper) `elem` [S.Det, S.Semidet]
          && shapeOk key (IM.elems (P.predClauses helper))
  Nothing -> False

-- | @app([], L, L). app([H|T], L, [H|R]) :- app(T, L, R).@
isAppendDef :: PredKey -> [S.Clause] -> Bool
isAppendDef (name, 3) [cBase, cStep]
  | S.Compound bName [S.Atom "nil", S.Var bL1, S.Var bL2] <- S.clauseHead cBase,
    bName == name && bL1 == bL2 && null (S.clauseBody cBase),
    S.Compound sName [S.Compound "cons" [S.Var vH1, S.Var vT1], S.Var vL1, S.Compound "cons" [S.Var vH2, S.Var vR1]] <- S.clauseHead cStep,
    sName == name && vH1 == vH2,
    [S.Compound rName [S.Var vT2, S.Var vL2, S.Var vR2]] <- S.clauseBody cStep =
      rName == name && vT1 == vT2 && vL1 == vL2 && vR1 == vR2
isAppendDef _ _ = False

-- | @noatt(_, [], _). noatt(Q, [Q1|Qs], D) :- Q =\= Q1, D1 is Q1 - Q,
-- D1 =\= D, D2 is Q - Q1, D2 =\= D, D3 is D + 1, noatt(Q, Qs, D3).@
isNoattDef :: PredKey -> [S.Clause] -> Bool
isNoattDef (name, 3) [cBase, cStep]
  | S.Compound bName [S.Var bQ, S.Atom "nil", S.Var bD] <- S.clauseHead cBase,
    bName == name && null (S.clauseBody cBase) && (bQ /= bD || bQ < 0),
    S.Compound sName [S.Var vQ, S.Compound "cons" [S.Var vQ1, S.Var vQs], S.Var vD] <- S.clauseHead cStep,
    sName == name,
    [ S.Compound "neq" [S.Var vQa, S.Var vQ1a],
      S.Compound "is" [S.Var vD1, S.Compound "minus" [S.Var vQ1b, S.Var vQb]],
      S.Compound "neq" [S.Var vD1a, S.Var vDa],
      S.Compound "is" [S.Var vD2, S.Compound "minus" [S.Var vQc, S.Var vQ1c]],
      S.Compound "neq" [S.Var vD2a, S.Var vDb],
      S.Compound "is" [S.Var vD3, S.Compound "plus" [S.Var vDc, S.IntLit 1]],
      S.Compound rName [S.Var vQd, S.Var vQsa, S.Var vD3a]
      ] <- S.clauseBody cStep =
      rName == name
        && all (== vQ) [vQa, vQb, vQc, vQd]
        && all (== vQ1) [vQ1a, vQ1b, vQ1c]
        && vD1 == vD1a
        && vD2 == vD2a
        && vD3 == vD3a
        && all (== vD) [vDa, vDb, vDc]
        && vQs == vQsa
isNoattDef _ _ = False

-- ─── Runtime invocation and reconciliation ───────────────────────────────────

-- | Scratch slots (past state, budgets and arguments) holding the heap limit
-- and entry heap top of the kernel's last mid-span bailout.
scratchBailCapIdx, scratchBailHIdx :: Int
scratchBailCapIdx = 22
scratchBailHIdx = 23

invokeJitKernel :: Store -> Int -> Int -> JitKernel -> IO (Maybe (Int64, Int))
invokeJitKernel s currentDepth maxDepth kernel =
  fmap (\(c, d, _) -> (c, d)) <$> invokeJitKernelWith False s currentDepth maxDepth kernel

invokeJitKernelWith :: Bool -> Store -> Int -> Int -> JitKernel -> IO (Maybe (Int64, Int, Bool))
invokeJitKernelWith allowChoices s currentDepth maxDepth kernel
  | jkScan kernel == -3 = case jkLazy kernel of
      Nothing -> pure Nothing
      Just unit -> invokeJitKernelWith allowChoices s currentDepth maxDepth unit
  | Just stackRef <- jkStack kernel = invokeClauseUnit allowChoices s currentDepth maxDepth kernel stackRef
  | otherwise = withForeignPtr (jkScratch kernel) $ \basePtr -> do
    let statePtr = basePtr
        budgetsPtr = basePtr `plusInt64` 8
        argsPtr = basePtr `plusInt64` 10
        arity = jkArity kernel
    entryH <- heapTop s
    entryTR <- trailTop s
    entryHB <- hb s
    cap <- readReg s rCAP
    gcLim <- readReg s rGCLIM
    cPtr <- cellsPtr s
    tPtr <- trailPtr s
    tCap <- readReg s rTRAILCAP
    clp <- readReg s rCLP
    let cBase = fromIntegral (ptrToIntPtr cPtr) :: Int64
        tBase = fromIntegral (ptrToIntPtr tPtr) :: Int64
        entryCap = min cap gcLim
        effectiveCap = min cap (gcLim + 131072)
        depthRem = maxDepth - currentDepth
        allocRem = max 0 (effectiveCap - entryH - 16)
    bailCap <- peekElemOff basePtr scratchBailCapIdx
    bailH <- peekElemOff basePtr scratchBailHIdx
    let backoff = bailCap == fromIntegral effectiveCap && fromIntegral entryH >= bailH
    if backoff || depthRem < 1 || clp /= 0 || gcLim < initialCollectLimit || entryH + jkCellsPerIter kernel + 8 > entryCap || entryTR + 8 > tCap
      then pure Nothing
      else do
        pokeElemOff statePtr stateCellsIdx cBase
        pokeElemOff statePtr stateTrailIdx tBase
        pokeElemOff statePtr stateHIdx (fromIntegral entryH)
        pokeElemOff statePtr stateTRIdx (fromIntegral entryTR)
        pokeElemOff statePtr stateHBIdx (fromIntegral (max entryHB entryH))
        pokeElemOff statePtr stateCapIdx (fromIntegral effectiveCap)
        pokeElemOff statePtr stateTrailCapIdx (fromIntegral tCap)
        pokeElemOff statePtr stateClpIdx (fromIntegral clp)
        pokeElemOff budgetsPtr budgetDepthIdx (fromIntegral depthRem)
        pokeElemOff budgetsPtr budgetAllocIdx (fromIntegral allocRem)
        forM_ [0 .. arity - 1] $ \i -> do
          w <- readArg s i
          pokeElemOff argsPtr i (fromIntegral w)
        code <- callNativeFn (jkFunPtr kernel) statePtr argsPtr budgetsPtr
        case code of
          c | c == jitSuccess -> do
                newH <- fromIntegral <$> peekElemOff statePtr stateHIdx
                newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
                depthAfter <- fromIntegral <$> peekElemOff budgetsPtr budgetDepthIdx
                setHeapTop s newH
                setTrailTop s newTR
                recordXcheck kernel arity argsPtr newH newTR depthAfter code
                pure (Just (jitSuccess, maxDepth - depthAfter, False))
            | c == jitFailure -> do
                newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
                setTrailTop s newTR
                unwindTrail s entryTR
                setHeapTop s entryH
                pure (Just (jitFailure, currentDepth, False))
            | c == jitExhausted -> do
                newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
                setTrailTop s newTR
                unwindTrail s entryTR
                setHeapTop s entryH
                pure (Just (jitExhausted, maxDepth + 1, False))
            | c == jitDeclined ->
                pure Nothing
            | otherwise -> do
                newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
                setTrailTop s newTR
                unwindTrail s entryTR
                setHeapTop s entryH
                pokeElemOff basePtr scratchBailCapIdx (fromIntegral effectiveCap)
                pokeElemOff basePtr scratchBailHIdx (fromIntegral entryH)
                jitDebug (show (jkKey kernel) ++ ": mid-span bailout -> interpreter")
                pure Nothing
  where
    plusInt64 :: Ptr Int64 -> Int -> Ptr Int64
    plusInt64 p n = intPtrToPtr (ptrToIntPtr p + fromIntegral (n * 8))

-- | Call a clause unit. The same entry conditions and outcomes as a shape
-- kernel, plus the native stack: a unit that runs out of it is unwound and
-- called again with a larger one. A unit returns 'jitError' for a value it
-- does not handle (a type, an unbound input it must test, a structure an
-- occurs check would walk): the call reruns on the interpreter, without the
-- capacity backoff, which is for a heap limit that would stop it again.
invokeClauseUnit :: Bool -> Store -> Int -> Int -> JitKernel -> IORef (ForeignPtr Int64, Int) -> IO (Maybe (Int64, Int, Bool))
invokeClauseUnit allowChoices s currentDepth maxDepth kernel stackRef =
  withForeignPtr (jkScratch kernel) $ \basePtr -> do
    let statePtr = basePtr
        budgetsPtr = basePtr `plusInt64` cuBudgetsAt
        argsPtr = basePtr `plusInt64` cuArgsAt
        arity = jkArity kernel
    entryH <- heapTop s
    entryTR <- trailTop s
    entryHB <- hb s
    cap <- readReg s rCAP
    gcLim <- readReg s rGCLIM
    tCap <- readReg s rTRAILCAP
    clp <- readReg s rCLP
    let effectiveCap = min cap gcLim
        depthRem = maxDepth - currentDepth
        bailIdx = cuStateWords + 2 + argSlotsOf kernel
    bailCap <- peekElemOff basePtr bailIdx
    bailH <- peekElemOff basePtr (bailIdx + 1)
    needsChoices <- if allowChoices then pure 0 else peekElemOff basePtr (bailIdx + 2)
    let backoff = needsChoices /= 0 || (bailH == 0 && bailCap > 0) || (bailCap == fromIntegral effectiveCap && fromIntegral entryH >= bailH)
    if backoff || depthRem < 1 || clp /= 0 || gcLim < initialCollectLimit || entryH + 8 > effectiveCap || entryTR + 8 > tCap
      then pure Nothing
      else do
        -- Native calls reuse the argument slots, so a retry after the
        -- stack grows must load the call's arguments again.
        let attempt = do
              forM_ [0 .. arity - 1] $ \i -> readArg s i >>= pokeElemOff argsPtr i . fromIntegral
              (stack, size) <- readIORef stackRef
              cPtr <- cellsPtr s
              tPtr <- trailPtr s
              code <- withForeignPtr stack $ \stackPtr -> do
                let stackBase = fromIntegral (ptrToIntPtr stackPtr) :: Int64
                pokeElemOff statePtr stateCellsIdx (fromIntegral (ptrToIntPtr cPtr))
                pokeElemOff statePtr stateTrailIdx (fromIntegral (ptrToIntPtr tPtr))
                pokeElemOff statePtr stateHIdx (fromIntegral entryH)
                pokeElemOff statePtr stateTRIdx (fromIntegral entryTR)
                pokeElemOff statePtr stateHBIdx (fromIntegral (max entryHB entryH))
                pokeElemOff statePtr stateCapIdx (fromIntegral effectiveCap)
                pokeElemOff statePtr stateTrailCapIdx (fromIntegral tCap)
                pokeElemOff statePtr stateClpIdx (fromIntegral clp)
                pokeElemOff statePtr stateNStackBaseIdx stackBase
                pokeElemOff statePtr stateNStackLimIdx (stackBase + fromIntegral (8 * size))
                pokeElemOff statePtr stateBIdx 0
                pokeElemOff statePtr stateAllowChoicesIdx (if allowChoices then 1 else 0)
                pokeElemOff budgetsPtr budgetDepthIdx (fromIntegral depthRem)
                pokeElemOff budgetsPtr budgetAllocIdx 0
                callNativeFn (jkFunPtr kernel) statePtr argsPtr budgetsPtr
              newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
              let unwind = setTrailTop s newTR >> unwindTrail s entryTR >> setHeapTop s entryH
              case code of
                c
                  | c == jitSuccess -> do
                      newH <- fromIntegral <$> peekElemOff statePtr stateHIdx
                      newB <- peekElemOff statePtr stateBIdx
                      setHeapTop s newH
                      setTrailTop s newTR
                      pure (Just (jitSuccess, currentDepth, newB /= 0))
                  | c == jitFailure -> unwind >> pure (Just (jitFailure, currentDepth, False))
                  | c == jitExhausted -> unwind >> pure (Just (jitExhausted, maxDepth + 1, False))
                  | c == jitDeclined -> pure Nothing
                  | c == jitStackFull, size < cuMaxStack -> do
                      unwind
                      grown <- mallocForeignPtrArray (size * 4)
                      writeIORef stackRef (grown, size * 4)
                      jitDebug (show (jkKey kernel) ++ ": native stack grown to " ++ show (size * 4) ++ " words")
                      attempt
                  | c == jitBailout -> do
                      unwind
                      pokeElemOff basePtr bailIdx (fromIntegral effectiveCap)
                      pokeElemOff basePtr (bailIdx + 1) (if effectiveCap - entryH > 65536 then 0 else fromIntegral entryH)
                      jitDebug (show (jkKey kernel) ++ ": heap limit -> interpreter")
                      pure Nothing
                  | c == 7 -> do
                      unwind
                      pokeElemOff basePtr (bailIdx + 2) 1
                      pure Nothing
                  | otherwise -> do
                      unwind
                      jitDebug (show (jkKey kernel) ++ ": rerun on the interpreter (code " ++ show c ++ ")")
                      pure Nothing
        attempt
  where
    plusInt64 :: Ptr Int64 -> Int -> Ptr Int64
    plusInt64 p n = intPtrToPtr (ptrToIntPtr p + fromIntegral (n * 8))

-- | Resume a clause unit at its topmost native choice frame (@stateBIdx@).
resumeClauseUnit :: Store -> Int -> Int -> Int -> Int -> JitKernel -> IO (Maybe (Int64, Int, Bool))
resumeClauseUnit s entryH entryTR currentDepth maxDepth kernel
  | jkScan kernel == -3 = case jkLazy kernel of
      Nothing -> pure Nothing
      Just unit -> resumeClauseUnit s entryH entryTR currentDepth maxDepth unit
  | Just stackRef <- jkStack kernel =
      withForeignPtr (jkScratch kernel) $ \basePtr -> do
        let statePtr = basePtr
            budgetsPtr = basePtr `plusInt64` cuBudgetsAt
            argsPtr = basePtr `plusInt64` cuArgsAt
        curH <- heapTop s
        curTR <- trailTop s
        cap <- readReg s rCAP
        gcLim <- readReg s rGCLIM
        tCap <- readReg s rTRAILCAP
        cPtr <- cellsPtr s
        tPtr <- trailPtr s
        (stack, _) <- readIORef stackRef
        code <- withForeignPtr stack $ \_ -> do
          pokeElemOff statePtr stateCellsIdx (fromIntegral (ptrToIntPtr cPtr))
          pokeElemOff statePtr stateTrailIdx (fromIntegral (ptrToIntPtr tPtr))
          pokeElemOff statePtr stateHIdx (fromIntegral curH)
          pokeElemOff statePtr stateTRIdx (fromIntegral curTR)
          pokeElemOff statePtr stateCapIdx (fromIntegral (min cap gcLim))
          pokeElemOff statePtr stateTrailCapIdx (fromIntegral tCap)
          pokeElemOff statePtr stateAllowChoicesIdx 1
          callNativeFn (jkFunPtr kernel) statePtr argsPtr budgetsPtr
        newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
        let unwind = setTrailTop s newTR >> unwindTrail s entryTR >> setHeapTop s entryH
        case code of
          c
            | c == jitSuccess -> do
                newH <- fromIntegral <$> peekElemOff statePtr stateHIdx
                newB <- peekElemOff statePtr stateBIdx
                setHeapTop s newH
                setTrailTop s newTR
                pure (Just (jitSuccess, currentDepth, newB /= 0))
            | c == jitFailure -> unwind >> pure (Just (jitFailure, currentDepth, False))
            | c == jitExhausted -> unwind >> pure (Just (jitExhausted, maxDepth + 1, False))
            | otherwise -> unwind >> pure Nothing
  | otherwise = pure Nothing
  where
    plusInt64 :: Ptr Int64 -> Int -> Ptr Int64
    plusInt64 p n = intPtrToPtr (ptrToIntPtr p + fromIntegral (n * 8))

-- | A clause unit's argument slots: its scratch block is laid out as
-- 'installClauseUnit' made it.
argSlotsOf :: JitKernel -> Int
argSlotsOf kernel = jkCellsPerIter kernel

recordXcheck :: JitKernel -> Int -> Ptr Int64 -> Int -> Int -> Int -> Int64 -> IO ()
recordXcheck kernel arity argsPtr newH newTR depthAfter code =
  forM_ jitXcheckDir $ \dir -> do
    seqNum <- atomicModifyIORef' xcheckSeq (\n -> (n + 1, n))
    args <- mapM (peekElemOff argsPtr) [0 .. arity - 1]
    let (name, ar) = jkKey kernel
        header =
          [ 0x494E464A49540001 :: Int64,
            fromIntegral ar,
            fromIntegral newH,
            fromIntegral newTR,
            fromIntegral depthAfter,
            code
          ]
            ++ args
        path = dir ++ "/" ++ name ++ "_" ++ show ar ++ "." ++ show seqNum ++ ".case"
    withBinaryFile path WriteMode $ \h ->
      withArrayLen header $ \cnt p -> hPutBuf h p (cnt * 8)

-- ─── List-search kernels (nondeterministic) ──────────────────────────────────

-- | A list search: two clauses, a base clause first whose list argument is a
-- prefix of elements unified with other arguments, then a step clause that
-- drops the head and recurses on the tail with the other arguments
-- unchanged:
--
-- > mem X [X | _].                    right_of X Y [Y, X | _].
-- > mem X [_ | T] <- mem X T.         right_of X Y [_ | T] <- right_of X Y T.
--
-- The kernel walks the list from the call's list argument, trying the base
-- clause's head at each position and undoing a failed attempt from the
-- trail itself. It returns at the first position where the head matches,
-- leaving that position's cons in the list argument's slot, and the caller
-- pushes a choice point that resumes with the step clause there; it returns
-- 'jitFailure' when the list ends, and 'jitBailout' with the current
-- position in the slot when the rest of the search needs the interpreter (an
-- unbound tail, nested structures, boxed constants, a full trail). Every
-- outcome is one the interpreter would reach: the step clause makes calls at
-- later positions exactly calls on the remaining list.
--
-- The result is the list argument's position and the base clause's
-- elements, each the argument it unifies with or 'Nothing' for @_@.
scanShape :: PredKey -> [S.Clause] -> Maybe (Int, [Maybe Int])
scanShape (name, arity) [cBase, cStep]
  | arity >= 1 && arity <= 8,
    S.Compound bName bArgs <- S.clauseHead cBase,
    bName == name && length bArgs == arity && null (S.clauseBody cBase),
    S.Compound sName sArgs <- S.clauseHead cStep,
    sName == name && length sArgs == arity,
    [S.Compound rName rArgs] <- S.clauseBody cStep,
    rName == name && length rArgs == arity =
      case [pos | pos <- [0 .. arity - 1], stepAt pos sArgs rArgs] of
        pos : _ -> do
          let others = [(i, a) | (i, a) <- zip [0 ..] bArgs, i /= pos]
          vars <- mapM (\(i, a) -> case a of S.Var v | v >= 0 -> Just (v, i); S.Var _ -> Just (-1, i); _ -> Nothing) others
          let named = [v | (v, _) <- vars, v >= 0]
          if length (nub named) /= length named then Nothing else Just ()
          elems <- prefix (bArgs !! pos)
          pattern <- mapM (element vars) elems
          if null pattern then Nothing else Just (pos, pattern)
        [] -> Nothing
  where
    stepAt pos sArgs rArgs
      | S.Compound "cons" [S.Var h, S.Var t] <- sArgs !! pos,
        t >= 0 && isAnonOrSingleton h cStep,
        rArgs !! pos == S.Var t =
          let others = [(a, b) | (i, a, b) <- zip3 [0 ..] sArgs rArgs, i /= pos]
              vs = [v | (S.Var v, S.Var v') <- others, v == v', v >= 0, v /= t]
           in length vs == length others && length (nub vs) == length vs
      | otherwise = False
    prefix = \case
      S.Compound "cons" [e, rest] -> (e :) <$> prefix rest
      S.Var v | isAnonOrSingleton v cBase -> Just []
      _ -> Nothing
    element vars = \case
      S.Var v
        | isAnonOrSingleton v cBase -> Just Nothing
        | Just i <- lookup v vars -> Just (Just i)
      _ -> Nothing
scanShape _ _ = Nothing

-- | The native code of a list search ('scanShape'). Arguments stay in their
-- slots; two slots past them hold the trail mark of the current attempt and
-- the cons being matched.
compileScanKernel :: Word' -> Int -> Int -> [Maybe Int] -> JitUnit
compileScanKernel consW arity pos pattern =
  JitUnit $
    [ JLoadImm RT0 RState stateClpIdx,
      JBranchImm JNe RT0 0 "decline",
      JLoadImm RT0 RArgs pos,
      JDeref RT0 RT0,
      JTagOf RT1 RT0,
      JBranchImm JEq RT1 (fromIntegral tagRef) "decline",
      JLabel "scan",
      JTagOf RT1 RT0,
      JBranchImm JEq RT1 (fromIntegral tagRef) "bail_here"
    ]
      ++ consCheck RT0 RT1 RT2 "fail"
      ++ [JStoreImm RTR RArgs spillTR, JStoreImm RT0 RArgs spillCons]
      ++ concat (zipWith element [0 :: Int ..] pattern)
      ++ [ JStoreImm RT0 RArgs pos,
           JReturn jitSuccess,
           JLabel "elem_fail"
         ]
      ++ unwind "uf"
      ++ [ JValOf RT1 RT0,
           JAddImm RT1 RT1 2,
           JLoadIx RT0 RCells RT1,
           JDeref RT0 RT0,
           JJump "scan",
           JLabel "elem_bail"
         ]
      ++ unwind "ub"
      ++ [ JLabel "bail_here",
           JStoreImm RT0 RArgs pos,
           JReturn jitBailout,
           JLabel "fail",
           JReturn jitFailure,
           JLabel "decline",
           JReturn jitDeclined
         ]
  where
    spillTR = arity
    spillCons = arity + 1
    consPlain = fromIntegral consW :: Int64
    consGround = fromIntegral (consW .|. groundBit) :: Int64
    gnd = fromIntegral groundBit :: Int64
    arityMask = 0x7FFFF :: Int64
    -- @w@ is a cons, else jump to @miss@ (an unbound @w@ is the
    -- caller's to handle first).
    consCheck w t1 t2 miss =
      [ JTagOf t1 w,
        JBranchImm JNe t1 (fromIntegral tagStr) miss,
        JValOf t1 w,
        JLoadIx t2 RCells t1,
        JBranchImm JEq t2 consPlain (lbl "cons"),
        JBranchImm JEq t2 consGround (lbl "cons"),
        JJump miss,
        JLabel (lbl "cons")
      ]
      where
        lbl x = x ++ "_" ++ show w ++ "_" ++ miss
    element j mp =
      [ op
        | j > 0,
          op <-
            [ JLoadImm RT1 RArgs spillCons,
              JValOf RT1 RT1,
              JAddImm RT1 RT1 2,
              JLoadIx RT1 RCells RT1,
              JDeref RT1 RT1,
              JTagOf RT2 RT1,
              JBranchImm JEq RT2 (fromIntegral tagRef) "elem_bail"
            ]
              ++ renameLabels ("e" ++ show j) (consCheck RT1 RT2 RT3 "elem_fail")
              ++ [JStoreImm RT1 RArgs spillCons]
      ]
        ++ case mp of
          Nothing -> []
          Just p ->
            [ JLoadImm RT2 RArgs spillCons,
              JValOf RT2 RT2,
              JAddImm RT2 RT2 1,
              JLoadIx RT2 RCells RT2,
              JLoadImm RT1 RArgs p
            ]
              ++ unifyShallow ("u" ++ show j)
    renameLabels pfx = map $ \case
      JLabel l | l /= "elem_fail" -> JLabel (pfx ++ l)
      JBranchImm c r v l | isLocal l -> JBranchImm c r v (pfx ++ l)
      JJump l | isLocal l -> JJump (pfx ++ l)
      op -> op
      where
        isLocal l = take 5 l == "cons_"
    unwind p =
      [ JLoadImm RT1 RArgs spillTR,
        JLabel (p ++ "_loop"),
        JBranchCmp JLe RTR RT1 (p ++ "_done"),
        JSubImm RTR RTR 1,
        JLoadIx RT2 RTrail RTR,
        JShr RT2 RT2 1,
        JMkWord RT3 RT2 0,
        JStoreIx RT3 RCells RT2,
        JJump (p ++ "_loop"),
        JLabel (p ++ "_done")
      ]
    -- Unify RT1 with RT2, one level deep: constants, unbound variables and
    -- structures whose arguments are constants, variables or ground
    -- structures. Anything deeper bails. Uses RT1-RT7.
    unifyShallow u =
      [ JDeref RT1 RT1,
        JDeref RT2 RT2,
        JBranchCmp JEq RT1 RT2 done,
        JTagOf RT3 RT1,
        JTagOf RT4 RT2,
        JBranchImm JEq RT3 (fromIntegral tagRef) aref,
        JBranchImm JEq RT4 (fromIntegral tagRef) bref,
        JBranchImm JNe RT3 (fromIntegral tagStr) atomic,
        JBranchImm JNe RT4 (fromIntegral tagStr) "elem_fail",
        JValOf RT1 RT1,
        JValOf RT2 RT2,
        JLoadIx RT3 RCells RT1,
        JLoadIx RT4 RCells RT2,
        JMovImm RT5 (fromIntegral (complement groundBit)),
        JAnd RT3 RT3 RT5,
        JAnd RT4 RT4 RT5,
        JBranchCmp JNe RT3 RT4 "elem_fail",
        JValOf RT3 RT3,
        JMovImm RT5 arityMask,
        JAnd RT3 RT3 RT5,
        JLabel loop,
        JBranchImm JEq RT3 0 done,
        JAddImm RT1 RT1 1,
        JAddImm RT2 RT2 1,
        JLoadIx RT4 RCells RT1,
        JLoadIx RT5 RCells RT2,
        JDeref RT4 RT4,
        JDeref RT5 RT5,
        JBranchCmp JEq RT4 RT5 next,
        JTagOf RT6 RT4,
        JBranchImm JEq RT6 (fromIntegral tagRef) xref,
        JTagOf RT7 RT5,
        JBranchImm JEq RT7 (fromIntegral tagRef) yref,
        -- Two different non-variables: two structures or two boxed
        -- constants need the interpreter; anything else is a mismatch.
        JBranchCmp JNe RT6 RT7 "elem_fail",
        JBranchImm JEq RT6 (fromIntegral tagStr) "elem_bail",
        JBranchImm JEq RT6 (fromIntegral tagBox) "elem_bail",
        JJump "elem_fail",
        JLabel xref
      ]
        ++ bindArg (u ++ "_x") RT4 RT5
        ++ [JLabel yref]
        ++ bindArg (u ++ "_y") RT5 RT4
        ++ [ JLabel next,
             JSubImm RT3 RT3 1,
             JJump loop,
             JLabel atomic,
             JBranchCmp JNe RT3 RT4 "elem_fail",
             JBranchImm JEq RT3 (fromIntegral tagBox) "elem_bail",
             JJump "elem_fail",
             JLabel aref
           ]
        ++ bindTop (u ++ "_a") RT1 RT2
        ++ [JLabel bref]
        ++ bindTop (u ++ "_b") RT2 RT1
        ++ [JLabel done]
      where
        done = u ++ "_done"
        loop = u ++ "_loop"
        next = u ++ "_next"
        xref = u ++ "_xref"
        yref = u ++ "_yref"
        aref = u ++ "_aref"
        bref = u ++ "_bref"
        atomic = u ++ "_atomic"
        -- An argument variable @v@ against a different word @o@: two
        -- variables bind the younger to the older, as 'unify' does; a
        -- structure needs the occurs check unless it is marked ground.
        bindArg p v o =
          [ JTagOf RT7 o,
            JBranchImm JNe RT7 (fromIntegral tagRef) (p ++ "_nonref"),
            JBranchCmp JGt v o (p ++ "_young"),
            JValOf RT6 o,
            JBindRef RT6 v "elem_bail",
            JJump next,
            JLabel (p ++ "_young"),
            JValOf RT6 v,
            JBindRef RT6 o "elem_bail",
            JJump next,
            JLabel (p ++ "_nonref"),
            JBranchImm JNe RT7 (fromIntegral tagStr) (p ++ "_bind"),
            JValOf RT6 o,
            JLoadIx RT6 RCells RT6,
            JMovImm RT7 gnd,
            JAnd RT6 RT6 RT7,
            JBranchImm JEq RT6 0 "elem_bail",
            JLabel (p ++ "_bind"),
            JValOf RT6 v,
            JBindRef RT6 o "elem_bail",
            JJump next
          ]
        -- The top-level variable @a@ against a different word @b@. A
        -- structure that is not marked ground gets the occurs check over its
        -- arguments: @a@ among them fails, a nested structure that is not
        -- marked ground bails.
        bindTop p a b =
          [ JTagOf RT3 b,
            JBranchImm JNe RT3 (fromIntegral tagRef) (p ++ "_nonref"),
            JBranchCmp JGt a b (p ++ "_young"),
            JValOf RT3 b,
            JBindRef RT3 a "elem_bail",
            JJump done,
            JLabel (p ++ "_young"),
            JValOf RT3 a,
            JBindRef RT3 b "elem_bail",
            JJump done,
            JLabel (p ++ "_nonref"),
            JBranchImm JNe RT3 (fromIntegral tagStr) (p ++ "_bind"),
            JValOf RT4 b,
            JLoadIx RT5 RCells RT4,
            JMovImm RT6 gnd,
            JAnd RT6 RT5 RT6,
            JBranchImm JNe RT6 0 (p ++ "_bind"),
            JValOf RT5 RT5,
            JMovImm RT6 arityMask,
            JAnd RT5 RT5 RT6,
            JLabel (p ++ "_occurs"),
            JBranchImm JEq RT5 0 (p ++ "_bind"),
            JAddImm RT4 RT4 1,
            JLoadIx RT6 RCells RT4,
            JDeref RT6 RT6,
            JBranchCmp JEq RT6 a "elem_fail",
            JTagOf RT7 RT6,
            JBranchImm JNe RT7 (fromIntegral tagStr) (p ++ "_onext"),
            JValOf RT7 RT6,
            JLoadIx RT7 RCells RT7,
            JMovImm RT6 gnd,
            JAnd RT7 RT7 RT6,
            JBranchImm JEq RT7 0 "elem_bail",
            JLabel (p ++ "_onext"),
            JSubImm RT5 RT5 1,
            JJump (p ++ "_occurs"),
            JLabel (p ++ "_bind"),
            JValOf RT3 a,
            JBindRef RT3 b "elem_bail",
            JJump done
          ]

-- | Run a list-search kernel on the argument registers. The result is the
-- kernel's code and the word it left in the list argument's slot: the
-- matched cons after 'jitSuccess', the position to continue from after
-- 'jitBailout'. On success the bindings of the matched head stay, trailed
-- against the entry heap top so that a choice point with the entry marks
-- undoes them; every other outcome leaves the trail as it was.
invokeScanKernel :: Store -> JitKernel -> IO (Int64, Word')
invokeScanKernel s kernel =
  withForeignPtr (jkScratch kernel) $ \basePtr -> do
    let statePtr = basePtr
        argsPtr = basePtr `plusInt64` 10
        arity = jkArity kernel
    entryH <- heapTop s
    entryTR <- trailTop s
    entryHB <- hb s
    cPtr <- cellsPtr s
    tPtr <- trailPtr s
    tCap <- readReg s rTRAILCAP
    clp <- readReg s rCLP
    pokeElemOff statePtr stateCellsIdx (fromIntegral (ptrToIntPtr cPtr))
    pokeElemOff statePtr stateTrailIdx (fromIntegral (ptrToIntPtr tPtr))
    pokeElemOff statePtr stateHIdx (fromIntegral entryH)
    pokeElemOff statePtr stateTRIdx (fromIntegral entryTR)
    pokeElemOff statePtr stateHBIdx (fromIntegral (max entryHB entryH))
    pokeElemOff statePtr stateTrailCapIdx (fromIntegral tCap)
    pokeElemOff statePtr stateClpIdx (fromIntegral clp)
    forM_ [0 .. arity - 1] $ \i -> do
      w <- readArg s i
      pokeElemOff argsPtr i (fromIntegral w)
    code <- callNativeFn (jkFunPtr kernel) statePtr argsPtr (basePtr `plusInt64` 8)
    newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
    setTrailTop s newTR
    w <- fromIntegral <$> peekElemOff argsPtr (jkScan kernel)
    pure (code, w)
  where
    plusInt64 :: Ptr Int64 -> Int -> Ptr Int64
    plusInt64 p n = intPtrToPtr (ptrToIntPtr p + fromIntegral (n * 8))
