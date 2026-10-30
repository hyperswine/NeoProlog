{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE LambdaCase #-}

-- | Step 3 + Track 2 native JIT tier for deterministic predicates in the Core engine.
--
-- Adapted from fprisc:compiler/Sol/HandJIT.hs and Sol/JitCore.hs
-- Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
--
-- Compiles admissible deterministic predicates to native machine code
-- (AArch64 and x86-64) at program load time:
--
-- * Slice 1: tail-recursive integer loops (@loop/1@, countdown/countup,
--   accumulator reductions over @INT@ with @is@ and comparisons).
-- * Fragment Growth 1: tail-recursive list/structure traversal and
--   construction (@app/3@, @range/3@) with ground-memo preservation and
--   freshness-proven occurs-check elision.
-- * Fragment Growth 2 (Track 2): nested deterministic list callers (@safe/1@
--   calling @noatt/3@, @nrev/2@ calling @app/3@) verified against the callee
--   definition in 'P.Program'.
-- * Fragment Growth 3: @semidet@ comparison/disequality tail loops over
--   ground lists (@noatt/3@).
--
-- Every non-admissible predicate or unexpected runtime tag/overflow silently
-- declines (pre-flight) or bails out (mid-span, unwinding trail and heap to
-- entry marks) to the Core interpreter.
module Infera.Core.Jit
  ( JitKernel (..),
    jitEnabled,
    jitDebugOn,
    compileJitKernel,
    invokeJitKernel,
  )
where

import Control.Monad (forM_, when)
import Data.Bits ((.|.))
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Int (Int64)
import qualified Data.IntMap.Strict as IM
import Data.Word (Word8)
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrArray, withForeignPtr)
import Foreign.Marshal.Array (withArray, withArrayLen)
import Foreign.Ptr (FunPtr, Ptr, castPtrToFunPtr, intPtrToPtr, nullPtr, ptrToIntPtr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import Infera.Core.Jit.AsmA64 (assembleA64)
import Infera.Core.Jit.AsmX64 (assembleX64)
import Infera.Core.Jit.IR
import Infera.Core.Store
import Infera.Error (PredKey)
import qualified Infera.Program as P
import qualified Infera.Syntax as S
import System.Environment (lookupEnv)
import System.IO (IOMode (..), hPutBuf, hPutStrLn, stderr, withBinaryFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Info (arch)

foreign import ccall unsafe "infera_jit_alloc"
  c_inferaJitAlloc :: Ptr Word8 -> Int -> IO (Ptr Word8)

foreign import ccall unsafe "infera_jit_has_sse41"
  c_inferaJitHasSse41 :: IO Int

type NativeFn = Ptr Int64 -> Ptr Int64 -> Ptr Int64 -> IO Int64

foreign import ccall unsafe "dynamic"
  callNativeFn :: FunPtr NativeFn -> NativeFn

-- | Enabled by default on supported architectures unless @INFERA_JIT=0@.
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

-- | A compiled native kernel for a predicate.
data JitKernel = JitKernel
  { jkKey :: !PredKey,
    jkArity :: !Int,
    jkFunPtr :: !(FunPtr NativeFn),
    jkAddr :: !Int64,
    -- | Static cell allocation per iteration (0 for pure integer loops, 3 for cons-allocating loops)
    jkCellsPerIter :: !Int,
    -- | Reusable pinned buffer for (state[8], budgets[2], args[8])
    jkScratch :: !(ForeignPtr Int64),
    -- | 'jkScratch''s address, taken once at install. The field above keeps
    -- the block alive for as long as this kernel is reachable, so the hot
    -- path can skip 'withForeignPtr'.
    jkBase :: !(Ptr Int64)
  }

assembleHost :: JitUnit -> [Word8]
assembleHost unit = case arch of
  "aarch64" -> assembleA64 unit
  "x86_64" -> assembleX64 unit
  _ -> []

installUnit :: PredKey -> Int -> Int -> JitUnit -> IO (Maybe JitKernel)
installUnit key arity cellsPerIter unit
  | not jitEnabled = pure Nothing
  | otherwise = do
      let bytes = assembleHost unit
      if null bytes
        then pure Nothing
        else do
          ptr <- withArray bytes $ \pb -> c_inferaJitAlloc pb (length bytes)
          if ptr == nullPtr
            then do
              jitDebug (show key ++ ": infera_jit_alloc failed")
              pure Nothing
            else do
              scratch <- mallocForeignPtrArray 24
              let addr = fromIntegral (ptrToIntPtr ptr)
                  fnPtr = castPtrToFunPtr ptr
              base <- withForeignPtr scratch pure
              jitDebug (show key ++ ": compiled (" ++ show (length bytes) ++ " bytes, " ++ arch ++ ")")
              pure (Just (JitKernel key arity fnPtr addr cellsPerIter scratch base))

-- ─── Admissible predicate shapes and lowering ────────────────────────────────

isAdmissiblePred :: [P.Signature] -> P.Signature -> Bool
isAdmissiblePred decls inferred =
  (null decls || all (\sig -> P.sigDet sig `elem` [S.Det, S.Semidet]) decls)
    && P.sigDet inferred `elem` [S.Det, S.Semidet]

-- | Attempt to compile a predicate into a native 'JitKernel' at program load
-- time. Declines silently (or logs under @INFERA_JIT_DEBUG=1@) when the
-- predicate is outside the admissible deterministic fragment.
compileJitKernel :: Word' -> Word' -> P.Program -> PredKey -> [P.Signature] -> P.Signature -> [S.Clause] -> IO (Maybe JitKernel)
compileJitKernel nilW consW prog key decls inferred clauses
  | not jitEnabled = pure Nothing
  | not (null decls) && any (\sig -> P.sigDet sig `notElem` [S.Det, S.Semidet]) decls = do
      jitDebug (show key ++ ": declined (non-det declared contract)")
      pure Nothing
  | P.sigDet inferred `notElem` [S.Det, S.Semidet] = do
      jitDebug (show key ++ ": declined (inferred " ++ show (P.sigDet inferred) ++ ")")
      pure Nothing
  | Just (unit, cellsPerIter) <- matchCountdownLoop key clauses =
      installUnit key (snd key) cellsPerIter unit
  | Just (unit, cellsPerIter) <- matchAppendLoop nilW consW key clauses =
      installUnit key (snd key) cellsPerIter unit
  | Just (unit, cellsPerIter) <- matchRangeLoop nilW consW key clauses =
      installUnit key (snd key) cellsPerIter unit
  | Just (unit, cellsPerIter) <- matchNoattLoop nilW consW key clauses =
      installUnit key (snd key) cellsPerIter unit
  | Just (unit, cellsPerIter) <- matchSafeLoop nilW consW prog key clauses =
      installUnit key (snd key) cellsPerIter unit
  | Just (unit, cellsPerIter) <- matchNrevLoop nilW consW prog key clauses =
      installUnit key (snd key) cellsPerIter unit
  | otherwise = do
      jitDebug (show key ++ ": declined (outside initial JIT fragment)")
      pure Nothing

-- 1. Slice 1: Countdown integer tail loop
--    p 0.
--    p N <- N > 0, N1 is N - 1, p N1.
matchCountdownLoop :: PredKey -> [S.Clause] -> Maybe (JitUnit, Int)
matchCountdownLoop (name, 1) [cBase, cStep]
  | S.Compound bName [S.IntLit baseVal] <- S.clauseHead cBase,
    bName == name,
    null (S.clauseBody cBase),
    S.Compound sName [S.Var vN] <- S.clauseHead cStep,
    sName == name,
    [ S.Compound "gt" [S.Var vN1, S.IntLit guardVal],
      S.Compound "is" [S.Var vNext, S.Compound "minus" [S.Var vN2, S.IntLit stepVal]],
      S.Compound rName [S.Var vNext2]
      ] <- S.clauseBody cStep,
    vN == vN1 && vN == vN2 && vNext == vNext2 && rName == name && stepVal > 0 && baseVal == guardVal =
      Just
        ( JitUnit
            [ -- Pre-flight: decline if CLP is active
              JLoadImm RT0 RState stateClpIdx,
              JBranchImm JNe RT0 0 "decline",
              -- Deref args[0] into RT0
              JLoadImm RT0 RArgs 0,
              JDeref RT0 RT0,
              -- Check tagOf(RT0) == tagInt (3)
              JTagOf RT1 RT0,
              JBranchImm JNe RT1 (fromIntegral tagInt) "decline",
              -- Unbox N into RT0
              JValOf RT0 RT0,
              -- Loop header
              JLabel "loop",
              JBranchImm JEq RT0 (fromIntegral baseVal) "success",
              JBranchImm JLe RT0 (fromIntegral guardVal) "fail",
              -- Recursive resolution step: tick depth budget
              JTickDepth "exhausted",
              JSubImm RT0 RT0 (fromIntegral stepVal),
              JJump "loop",
              JLabel "success",
              JReturn jitSuccess,
              JLabel "fail",
              JReturn jitFailure,
              JLabel "decline",
              JReturn jitDeclined,
              JLabel "exhausted",
              JReturn jitExhausted
            ],
          0
        )
matchCountdownLoop _ _ = Nothing

-- 2. Fragment Growth #1a: List append tail loop (`app/3`)
--    app [] L L.
--    app [H | T] L [H | R] <- app T L R.
matchAppendLoop :: Word' -> Word' -> PredKey -> [S.Clause] -> Maybe (JitUnit, Int)
matchAppendLoop nilW consW (name, 3) [cBase, cStep]
  | S.Compound bName [S.Atom "nil", S.Var bL1, S.Var bL2] <- S.clauseHead cBase,
    bName == name && bL1 == bL2 && null (S.clauseBody cBase),
    S.Compound sName [S.Compound "cons" [S.Var vH1, S.Var vT1], S.Var vL1, S.Compound "cons" [S.Var vH2, S.Var vR1]] <- S.clauseHead cStep,
    sName == name && vH1 == vH2,
    [S.Compound rName [S.Var vT2, S.Var vL2, S.Var vR2]] <- S.clauseBody cStep,
    rName == name && vT1 == vT2 && vL1 == vL2 && vR1 == vR2 =
      let consGround = fromIntegral (consW .|. groundBit) :: Int64
          consPlain = fromIntegral consW :: Int64
          nilImm = fromIntegral nilW :: Int64
       in Just
            ( JitUnit
                [ -- Pre-flight: decline if CLP is active
                  JLoadImm RT0 RState stateClpIdx,
                  JBranchImm JNe RT0 0 "decline",
                  -- Load args[0] (list1), args[1] (list2), args[2] (out)
                  JLoadImm RT0 RArgs 0,
                  JDeref RT0 RT0,
                  JLoadImm RT1 RArgs 1,
                  JDeref RT1 RT1,
                  JLoadImm RT2 RArgs 2,
                  JDeref RT2 RT2,
                  -- Pre-flight check: RT2 must be an unbound REF (write mode)
                  -- and RT1 must be ground (nil, int, atm, chr, or ground STR)
                  -- so occurs check on the base-case bind is provably elided.
                  JTagOf RT3 RT2,
                  JBranchImm JNe RT3 (fromIntegral tagRef) "decline",
                  JBranchImm JEq RT1 nilImm "check_rt0",
                  JTagOf RT3 RT1,
                  JBranchImm JEq RT3 (fromIntegral tagStr) "check_rt1_str",
                  JBranchImm JEq RT3 (fromIntegral tagRef) "decline",
                  JJump "check_rt0",
                  JLabel "check_rt1_str",
                  JValOf RT4 RT1,
                  JLoadIx RT4 RCells RT4,
                  -- Require groundBit on RT1's functor cell
                  JBranchImm JEq RT4 consGround "check_rt0",
                  JJump "decline",
                  JLabel "check_rt0",
                  -- Pre-flight check: RT0 is either nil or STR
                  JBranchImm JEq RT0 nilImm "base_case",
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "decline",
                  -- Main append loop:
                  -- RT0 = current list1 word (dereferenced)
                  -- RT1 = list2 word (dereferenced, proven ground)
                  -- RT2 = current output REF word (dereferenced tagRef)
                  JLabel "loop",
                  JBranchImm JEq RT0 nilImm "base_case",
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "bailout",
                  JValOf RT3 RT0, -- RT3 = cell address of list1 cons block
                  JLoadIx RT4 RCells RT3, -- functor word
                  JBranchImm JEq RT4 consPlain "fun_ok",
                  JBranchImm JEq RT4 consGround "fun_ok",
                  JJump "bailout",
                  JLabel "fun_ok",
                  -- Check heap capacity: RH + 4 <= rCAP
                  JLoadImm RT4 RState stateCapIdx,
                  JAddImm RT5 RH 4,
                  JBranchCmp JGt RT5 RT4 "bailout",
                  -- Load H (RT4) and T (RT5) from list1 cell
                  JAddImm RT4 RT3 1,
                  JLoadIx RT4 RCells RT4,
                  JDeref RT4 RT4,
                  -- Binding the output to a structure that contains it would
                  -- create a cycle the interpreter rejects by occurs check.
                  -- Only copy atomic elements natively; anything compound or
                  -- still unbound goes back to the interpreter.
                  JTagOf RT5 RT4,
                  JBranchImm JEq RT5 (fromIntegral tagInt) "head_ok",
                  JBranchImm JEq RT5 (fromIntegral tagAtm) "head_ok",
                  JBranchImm JEq RT5 (fromIntegral tagChr) "head_ok",
                  JJump "bailout",
                  JLabel "head_ok",
                  JAddImm RT5 RT3 2,
                  JLoadIx RT5 RCells RT5,
                  JDeref RT5 RT5,
                  -- Allocate 3 cells at RH for new cons cell:
                  --   RCells[RH]     = consPlain (non-ground spine cell, matching buildCompound)
                  --   RCells[RH + 1] = H (RT4)
                  --   RCells[RH + 2] = refWord(RH + 2)
                  JMovImm RT3 consPlain,
                  JStoreIx RT3 RCells RH,
                  JAddImm RT3 RH 1,
                  JStoreIx RT4 RCells RT3,
                  JAddImm RT3 RH 2,
                  JMkWord RT4 RT3 tagRef,
                  JStoreIx RT4 RCells RT3,
                  -- Construct strWord(RH) in RT3 and bind output REF (valOf RT2)
                  JMkWord RT3 RH tagStr,
                  JAddImm RH RH 3,
                  JValOf RT2 RT2,
                  JBindRef RT2 RT3 "bailout",
                  -- Advance: RT2 = new tail refWord (RT4), RT0 = T (RT5)
                  JMov RT2 RT4,
                  JMov RT0 RT5,
                  JTickDepth "exhausted",
                  JJump "loop",
                  JLabel "base_case",
                  -- Bind current output REF (RT2) to RT1
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
matchAppendLoop _ _ _ _ = Nothing

-- 3. Fragment Growth #1b: Integer range list builder (`range/3`)
--    range N N [N].
--    range I N [I | T] <- I < N, I1 is I + 1, range I1 N T.
matchRangeLoop :: Word' -> Word' -> PredKey -> [S.Clause] -> Maybe (JitUnit, Int)
matchRangeLoop nilW consW (name, 3) [cBase, cStep]
  | S.Compound bName [S.Var bN1, S.Var bN2, S.Compound "cons" [S.Var bN3, S.Atom "nil"]] <- S.clauseHead cBase,
    bName == name && bN1 == bN2 && bN2 == bN3 && null (S.clauseBody cBase),
    S.Compound sName [S.Var vI1, S.Var vN1, S.Compound "cons" [S.Var vI2, S.Var vT1]] <- S.clauseHead cStep,
    sName == name && vI1 == vI2,
    [ S.Compound "lt" [S.Var vI3, S.Var vN2],
      S.Compound "is" [S.Var vI1Next, S.Compound "plus" [S.Var vI4, S.IntLit 1]],
      S.Compound rName [S.Var vI1Next2, S.Var vN3, S.Var vT2]
      ] <- S.clauseBody cStep,
    rName == name && vI1 == vI3 && vI1 == vI4 && vN1 == vN2 && vN1 == vN3 && vI1Next == vI1Next2 && vT1 == vT2 =
      let consGround = fromIntegral (consW .|. groundBit) :: Int64
          consPlain = fromIntegral consW :: Int64
          nilImm = fromIntegral nilW :: Int64
       in Just
            ( JitUnit
                [ JLoadImm RT0 RState stateClpIdx,
                  JBranchImm JNe RT0 0 "decline",
                  -- Deref args[0] (I), args[1] (N), args[2] (Out)
                  JLoadImm RT0 RArgs 0,
                  JDeref RT0 RT0,
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagInt) "decline",
                  JValOf RT0 RT0,
                  JLoadImm RT1 RArgs 1,
                  JDeref RT1 RT1,
                  JTagOf RT3 RT1,
                  JBranchImm JNe RT3 (fromIntegral tagInt) "decline",
                  JValOf RT1 RT1,
                  JLoadImm RT2 RArgs 2,
                  JDeref RT2 RT2,
                  JTagOf RT3 RT2,
                  JBranchImm JNe RT3 (fromIntegral tagRef) "decline",
                  -- Loop: RT0 = I (unboxed), RT1 = N (unboxed), RT2 = Out (tagRef word)
                  JLabel "loop",
                  JBranchCmp JEq RT0 RT1 "base_case",
                  JBranchCmp JGt RT0 RT1 "fail",
                  -- Check heap capacity: RH + 4 <= rCAP
                  JLoadImm RT4 RState stateCapIdx,
                  JAddImm RT5 RH 4,
                  JBranchCmp JGt RT5 RT4 "bailout",
                  -- Allocate [I | T] at RH
                  JMovImm RT3 consPlain,
                  JStoreIx RT3 RCells RH,
                  JMkWord RT4 RT0 tagInt,
                  JAddImm RT3 RH 1,
                  JStoreIx RT4 RCells RT3,
                  JAddImm RT3 RH 2,
                  JMkWord RT4 RT3 tagRef,
                  JStoreIx RT4 RCells RT3,
                  JMkWord RT3 RH tagStr,
                  JAddImm RH RH 3,
                  JValOf RT2 RT2,
                  JBindRef RT2 RT3 "bailout",
                  JMov RT2 RT4,
                  JAddImm RT0 RT0 1,
                  JTickDepth "exhausted",
                  JJump "loop",
                  JLabel "base_case",
                  -- Allocate ground [N] = cons(N, nil) at RH
                  JLoadImm RT4 RState stateCapIdx,
                  JAddImm RT5 RH 4,
                  JBranchCmp JGt RT5 RT4 "bailout",
                  JMovImm RT3 consGround,
                  JStoreIx RT3 RCells RH,
                  JMkWord RT4 RT0 tagInt,
                  JAddImm RT3 RH 1,
                  JStoreIx RT4 RCells RT3,
                  JAddImm RT3 RH 2,
                  JMovImm RT4 nilImm,
                  JStoreIx RT4 RCells RT3,
                  JMkWord RT3 RH tagStr,
                  JAddImm RH RH 3,
                  JValOf RT2 RT2,
                  JBindRef RT2 RT3 "bailout",
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
              3
            )
matchRangeLoop _ _ _ _ = Nothing

-- 4. Fragment Growth #3: Semidet comparison/disequality list loop (`noatt/3`)
--    noatt _ [] _.
--    noatt Q [Q1 | Qs] D <- Q != Q1, D1 is Q1 - Q, D1 != D, D2 is Q - Q1, D2 != D, D3 is D + 1, noatt Q Qs D3.
matchNoattLoop :: Word' -> Word' -> PredKey -> [S.Clause] -> Maybe (JitUnit, Int)
matchNoattLoop nilW consW (name, 3) [cBase, cStep]
  | S.Compound bName [_, S.Atom "nil", _] <- S.clauseHead cBase,
    bName == name && null (S.clauseBody cBase),
    S.Compound sName [S.Var vQ, S.Compound "cons" [S.Var vQ1, S.Var vQs], S.Var vD] <- S.clauseHead cStep,
    sName == name,
    [ S.Compound "neq" [S.Var vQa, S.Var vQ1a],
      S.Compound "is" [S.Var vD1, S.Compound "minus" [S.Var vQ1b, S.Var vQb]],
      S.Compound "neq" [S.Var vD1a, S.Var vDa],
      S.Compound "is" [S.Var vD2, S.Compound "minus" [S.Var vQc, S.Var vQ1c]],
      S.Compound "neq" [S.Var vD2a, S.Var vDb],
      S.Compound "is" [S.Var vD3, S.Compound "plus" [S.Var vDc, S.IntLit 1]],
      S.Compound rName [S.Var vQd, S.Var vQsa, S.Var vD3a]
      ] <- S.clauseBody cStep,
    rName == name
      && all (== vQ) [vQa, vQb, vQc, vQd]
      && all (== vQ1) [vQ1a, vQ1b, vQ1c]
      && vD1 == vD1a
      && vD2 == vD2a
      && vD3 == vD3a
      && all (== vD) [vDa, vDb, vDc]
      && vQs == vQsa =
      let consGround = fromIntegral (consW .|. groundBit) :: Int64
          consPlain = fromIntegral consW :: Int64
          nilImm = fromIntegral nilW :: Int64
       in Just
            ( JitUnit
                [ JLoadImm RT0 RState stateClpIdx,
                  JBranchImm JNe RT0 0 "decline",
                  -- args[0] = Q (int), args[1] = Qs (list), args[2] = D (int)
                  JLoadImm RT0 RArgs 0,
                  JDeref RT0 RT0,
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagInt) "decline",
                  JValOf RT0 RT0, -- RT0 = unboxed Q
                  JLoadImm RT1 RArgs 1,
                  JDeref RT1 RT1, -- RT1 = current list word
                  JLoadImm RT2 RArgs 2,
                  JDeref RT2 RT2,
                  JTagOf RT3 RT2,
                  JBranchImm JNe RT3 (fromIntegral tagInt) "decline",
                  JValOf RT2 RT2, -- RT2 = unboxed D
                  JLabel "loop",
                  JBranchImm JEq RT1 nilImm "success",
                  JTagOf RT3 RT1,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "bailout",
                  JValOf RT3 RT1,
                  JLoadIx RT4 RCells RT3,
                  JBranchImm JEq RT4 consPlain "cons_ok",
                  JBranchImm JEq RT4 consGround "cons_ok",
                  JJump "bailout",
                  JLabel "cons_ok",
                  -- Load Q1 (cell + 1) and Qs' (cell + 2)
                  JAddImm RT4 RT3 1,
                  JLoadIx RT4 RCells RT4,
                  JDeref RT4 RT4,
                  JTagOf RT5 RT4,
                  JBranchImm JNe RT5 (fromIntegral tagInt) "bailout",
                  JValOf RT4 RT4, -- RT4 = unboxed Q1
                  -- Check Q != Q1
                  JBranchCmp JEq RT0 RT4 "fail",
                  -- Check Q1 - Q != D
                  JSubChecked RT5 RT4 RT0 "bailout",
                  JBranchCmp JEq RT5 RT2 "fail",
                  -- Check Q - Q1 != D
                  JSubChecked RT5 RT0 RT4 "bailout",
                  JBranchCmp JEq RT5 RT2 "fail",
                  -- Advance Qs and D := D + 1
                  JAddImm RT5 RT3 2,
                  JLoadIx RT1 RCells RT5,
                  JDeref RT1 RT1,
                  JAddImm RT2 RT2 1,
                  JTickDepth "exhausted",
                  JJump "loop",
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
matchNoattLoop _ _ _ _ = Nothing

-- 5. Track 2A (Fragment Growth #2a): Nested list safety loop (`safe/1` calling `noatt/3`)
--    safe [].
--    safe [Q | Qs] <- noatt Q Qs 1, safe Qs.
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
    Just helperPred <- P.lookupPred (helperName, 3) prog,
    isAdmissiblePred (P.predDecls helperPred) (P.predInferred helperPred),
    Just _ <- matchNoattLoop     nilW consW (helperName, 3) (IM.elems (P.predClauses helperPred)) =
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
                  -- Outer loop over [Q | Qs] in RT0
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
                  -- Load Q into RT1 (unboxed) and Qs into RT0
                  JAddImm RT4 RT3 1,
                  JLoadIx RT1 RCells RT4,
                  JDeref RT1 RT1,
                  JTagOf RT5 RT1,
                  JBranchImm JNe RT5 (fromIntegral tagInt) "bailout",
                  JValOf RT1 RT1,
                  JAddImm RT4 RT3 2,
                  JLoadIx RT0 RCells RT4,
                  JDeref RT0 RT0,
                  -- Call noatt Q Qs initD: tick depth for noatt entry
                  JTickDepth "exhausted",
                  JMov RT2 RT0,
                  JMovImm RT6 (fromIntegral initD),
                  -- Inner loop over Qs' in RT2 with distance D in RT6
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
                  JTickDepth "exhausted",
                  JJump "inner_loop",
                  JLabel "inner_done",
                  -- Tail call safe Qs: tick depth
                  JTickDepth "exhausted",
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

-- 6. Track 2B (Fragment Growth #2b): Naive list reverse (`nrev/2` calling `app/3`)
--    nrev [] [].
--    nrev [H | T] R <- nrev T R1, app R1 [H] R.
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
    Just appPred <- P.lookupPred (appName, 3) prog,
    isAdmissiblePred (P.predDecls appPred) (P.predInferred appPred),
    Just _ <- matchAppendLoop     nilW consW (appName, 3) (IM.elems (P.predClauses appPred)) =
      let consGround = fromIntegral (consW .|. groundBit) :: Int64
          consPlain = fromIntegral consW :: Int64
          nilImm = fromIntegral nilW :: Int64
       in Just
            ( JitUnit
                [ JLoadImm RT0 RState stateClpIdx,
                  JBranchImm JNe RT0 0 "decline",
                  -- args[0] = input list, args[1] = output REF (write mode)
                  JLoadImm RT0 RArgs 0,
                  JDeref RT0 RT0,
                  JLoadImm RT2 RArgs 1,
                  JDeref RT2 RT2,
                  JTagOf RT3 RT2,
                  JBranchImm JNe RT3 (fromIntegral tagRef) "decline",
                  -- Check args[0] is nil or STR
                  JMovImm RT1 nilImm,
                  JBranchImm JEq RT0 nilImm "base_case",
                  JTagOf RT3 RT0,
                  JBranchImm JNe RT3 (fromIntegral tagStr) "decline",
                  -- RT0 = current input list word
                  -- RT1 = reversed accumulator list word (starts at nilImm)
                  -- RT2 = caller output REF word (bound only at base_case)
                  -- RT6 = step resolution depth cost (starts at 2: 1 for nrev + 1 for app base, +1 per element)
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
                  -- Check heap capacity: RH + 4 <= rCAP
                  JLoadImm RT4 RState stateCapIdx,
                  JAddImm RT5 RH 4,
                  JBranchCmp JGt RT5 RT4 "bailout",
                  -- Load H (RT4) and T (RT5)
                  JAddImm RT4 RT3 1,
                  JLoadIx RT4 RCells RT4,
                  JDeref RT4 RT4,
                  -- Same occurs-check concern as append: only atomic heads.
                  -- RT5 is free here; RT6 carries the depth step.
                  JTagOf RT5 RT4,
                  JBranchImm JEq RT5 (fromIntegral tagInt) "head_ok",
                  JBranchImm JEq RT5 (fromIntegral tagAtm) "head_ok",
                  JBranchImm JEq RT5 (fromIntegral tagChr) "head_ok",
                  JJump "bailout",
                  JLabel "head_ok",
                  JAddImm RT5 RT3 2,
                  JLoadIx RT5 RCells RT5,
                  JDeref RT5 RT5,
                  -- Allocate cons(H, RT1) at RH
                  JMovImm RT3 consPlain,
                  JStoreIx RT3 RCells RH,
                  JAddImm RT3 RH 1,
                  JStoreIx RT4 RCells RT3,
                  JAddImm RT3 RH 2,
                  JStoreIx RT1 RCells RT3,
                  JMkWord RT1 RH tagStr,
                  JAddImm RH RH 3,
                  -- Advance RT0 := T, tick resolution depth by RT6, and increment RT6
                  JMov RT0 RT5,
                  JTickDepthReg RT6 "exhausted",
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

-- ─── Runtime invocation and reconciliation ───────────────────────────────────

-- | Invoke a compiled native kernel and return the kernel's own return code,
-- with no boxed result to allocate on the way out:
--
-- * 'jitSuccess' (@1@): the call succeeded and the store carries the answer.
-- * 'jitFailure' (@0@): the call failed and the trail and heap are unwound.
-- * 'jitExhausted' (@3@): the resolution depth budget ran out.
-- * 'jitDeclined' (@2@) or 'jitBailout' (@4@): nothing was decided; the trail
--   and heap are unwound to the entry marks and the caller runs the
--   interpreter path unchanged. The caller treats both the same.
invokeJitKernel :: Store -> Int -> Int -> JitKernel -> IO Int64
invokeJitKernel s currentDepth maxDepth kernel = do
    let basePtr = jkBase kernel
        statePtr = basePtr
        budgetsPtr = basePtr `plusInt64` 8
        argsPtr = basePtr `plusInt64` 10
        arity = jkArity kernel
    entryH <- heapTop s
    entryTR <- trailTop s
    cap <- readReg s rCAP
    gcLim <- readReg s rGCLIM
    cPtr <- cellsPtr s
    tPtr <- trailPtr s
    tCap <- readReg s rTRAILCAP
    clp <- readReg s rCLP
    let cBase = fromIntegral (ptrToIntPtr cPtr) :: Int64
        tBase = fromIntegral (ptrToIntPtr tPtr) :: Int64
        effectiveCap = min cap gcLim
        depthRem = maxDepth - currentDepth
    -- Decline when CLP is active, when a small test GC limit (< initialCollectLimit)
    -- is in effect to exercise collector statistics, or when room is insufficient.
    if clp /= 0 || gcLim < initialCollectLimit || entryH + jkCellsPerIter kernel + 8 > effectiveCap || entryTR + 8 > tCap
      then pure jitDeclined
      else do
        pokeElemOff statePtr stateCellsIdx cBase
        pokeElemOff statePtr stateTrailIdx tBase
        pokeElemOff statePtr stateHIdx (fromIntegral entryH)
        pokeElemOff statePtr stateTRIdx (fromIntegral entryTR)
        -- Trail every cell the span can bind: a bailout rewinds the heap to
        -- entryH, so bindings at or above it are discarded, and anything below
        -- must be undone by the trail. The store's own boundary is the last
        -- choice point, which is older than entryH and would leave bindings
        -- of cells allocated since then neither trailed nor reset.
        pokeElemOff statePtr stateHBIdx (fromIntegral entryH)
        pokeElemOff statePtr stateCapIdx (fromIntegral effectiveCap)
        pokeElemOff statePtr stateTrailCapIdx (fromIntegral tCap)
        pokeElemOff statePtr stateClpIdx (fromIntegral clp)
        pokeElemOff budgetsPtr budgetDepthIdx (fromIntegral depthRem)
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
                pure jitSuccess
            | c == jitFailure -> do
                newH <- fromIntegral <$> peekElemOff statePtr stateHIdx
                newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
                setTrailTop s newTR
                unwindTrail s entryTR
                setHeapTop s entryH
                let _ = newH
                pure jitFailure
            | c == jitExhausted -> do
                newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
                setTrailTop s newTR
                unwindTrail s entryTR
                setHeapTop s entryH
                pure jitExhausted
            | c == jitDeclined ->
                pure jitDeclined
            | otherwise -> do
                -- Mid-span bailout: unwind trail and heap to entry marks and
                -- let the interpreter rerun the call cleanly.
                newTR <- fromIntegral <$> peekElemOff statePtr stateTRIdx
                setTrailTop s newTR
                unwindTrail s entryTR
                setHeapTop s entryH
                jitDebug (show (jkKey kernel) ++ ": mid-span bailout -> interpreter")
                pure jitBailout
  where
    plusInt64 :: Ptr Int64 -> Int -> Ptr Int64
    plusInt64 p n = intPtrToPtr (ptrToIntPtr p + fromIntegral (n * 8))

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
