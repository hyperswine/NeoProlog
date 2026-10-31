{-# LANGUAGE LambdaCase #-}

-- | x86-64 (SysV ABI) native code emitter for the Infera JIT tier.
--
-- Adapted from fprisc:compiler/Sol/AsmX64.hs
-- Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
--
-- Register mapping (SysV x86-64):
--   Entry parameters: rdi = state*, rsi = args*, rdx = budgets*
--   rbx = RState    (callee-saved)
--   r12 = RArgs     (callee-saved)
--   r13 = RDepth    (callee-saved cached budgets[0] resolution depth budget)
--   r14 = RCells    (callee-saved)
--   r15 = RTrail    (callee-saved)
--   r8  = RH        (caller-saved)
--   r9  = RTR       (caller-saved)
--   r10 = RHB       (caller-saved)
--   rcx = RT0       (caller-saved working register)
--   rsi = RT1       (caller-saved working register, after RArgs is saved to r12)
--   rdi = RT2       (caller-saved working register, after RState is saved to rbx)
--   rbp-8 .. rbp-40  = saved rbx, r12, r13, r14, r15 (pushed in the prologue)
--   rbp-48           = RBudgets pointer spill slot
--   rbp-56 .. rbp-88 = spilled slots for RT3..RT7 when needed
--   The spill area must stay below the callee-saved pushes: an earlier layout
--   put RBudgets at rbp-40, overwriting the saved r15 that GHC relies on.
--   rax, rdx, r11    = assembler scratch registers
module Infera.Core.Jit.AsmX64
  ( assembleX64,
  )
where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.Int (Int64)
import qualified Data.Map.Strict as M
import Data.Word (Word8)
import Infera.Core.Jit.IR

type B = [Word8]

imm32 :: Int -> B
imm32 v = [fromIntegral (v `shiftR` s .&. 0xFF) | s <- [0, 8, 16, 24]]

imm64 :: Int64 -> B
imm64 v = [fromIntegral (fromIntegral v `shiftR` s .&. (0xFF :: Integer)) | s <- [0, 8, 16, 24, 32, 40, 48, 56]]

hwLoc :: Reg -> Either Int Int
hwLoc = \case
  RState -> Left 3 -- rbx
  RArgs -> Left 12 -- r12
  RBudgets -> Right (-48) -- [rbp - 48]
  RCells -> Left 14 -- r14
  RTrail -> Left 15 -- r15
  RH -> Left 8 -- r8
  RTR -> Left 9 -- r9
  RHB -> Left 10 -- r10
  RT0 -> Left 1 -- rcx
  RT1 -> Left 6 -- rsi
  RT2 -> Left 7 -- rdi
  RT3 -> Right (-56)
  RT4 -> Right (-64)
  RT5 -> Right (-72)
  RT6 -> Right (-80)
  RT7 -> Right (-88)

rexW :: Int -> Int -> Int -> Word8
rexW r x b =
  0x48
    .|. (if r >= 8 then 0x04 else 0)
    .|. (if x >= 8 then 0x02 else 0)
    .|. (if b >= 8 then 0x01 else 0)

modRM :: Int -> Int -> Int -> Word8
modRM m reg rm =
  fromIntegral ((m `shiftL` 6) .|. ((reg .&. 7) `shiftL` 3) .|. (rm .&. 7))

sib :: Int -> Int -> Int -> Word8
sib scale idx base =
  fromIntegral ((scale `shiftL` 6) .|. ((idx .&. 7) `shiftL` 3) .|. (base .&. 7))

movRR :: Int -> Int -> B
movRR dst src
  | dst == src = []
  | otherwise = [rexW src 0 dst, 0x89, modRM 3 src dst]

loadRbp8 :: Int -> Int -> B
loadRbp8 dst disp = [rexW dst 0 5, 0x8B, modRM 1 dst 5, fromIntegral (disp .&. 0xFF)]

storeRbp8 :: Int -> Int -> B
storeRbp8 src disp = [rexW src 0 5, 0x89, modRM 1 src 5, fromIntegral (disp .&. 0xFF)]

getReg :: Int -> Reg -> (Int, B)
getReg tmp r = case hwLoc r of
  Left hw -> (hw, [])
  Right disp -> (tmp, loadRbp8 tmp disp)

putReg :: Reg -> Int -> B
putReg r hw = case hwLoc r of
  Left dst -> movRR dst hw
  Right disp -> storeRbp8 hw disp

movImm :: Int -> Int64 -> B
movImm dst v = [rexW 0 0 dst, 0xB8 + fromIntegral (dst .&. 7)] ++ imm64 v

loadImmIx :: Int -> Int -> Int -> B
loadImmIx dst base idx =
  let disp = idx * 8
      needSib = (base .&. 7) == 4
   in [rexW dst 0 base, 0x8B, modRM 1 dst base]
        ++ [sib 0 4 base | needSib]
        ++ [fromIntegral (disp .&. 0xFF)]

storeImmIx :: Int -> Int -> Int -> B
storeImmIx src base idx =
  let disp = idx * 8
      needSib = (base .&. 7) == 4
   in [rexW src 0 base, 0x89, modRM 1 src base]
        ++ [sib 0 4 base | needSib]
        ++ [fromIntegral (disp .&. 0xFF)]

loadRegIx :: Int -> Int -> Int -> B
loadRegIx dst base idx =
  let needDisp = (base .&. 7) == 5
      m = if needDisp then 1 else 0
   in [rexW dst idx base, 0x8B, modRM m dst 4, sib 3 idx base] ++ [0 | needDisp]

storeRegIx :: Int -> Int -> Int -> B
storeRegIx src base idx =
  let needDisp = (base .&. 7) == 5
      m = if needDisp then 1 else 0
   in [rexW src idx base, 0x89, modRM m src 4, sib 3 idx base] ++ [0 | needDisp]

cmpRR :: Int -> Int -> B
cmpRR a b = [rexW b 0 a, 0x39, modRM 3 b a]

shl3, sar3 :: Int -> B
shl3 r = [rexW 0 0 r, 0xC1, modRM 3 4 r, 3]
sar3 r = [rexW 0 0 r, 0xC1, modRM 3 7 r, 3]

and7 :: Int -> B
and7 r = [rexW 0 0 r, 0x83, modRM 3 4 r, 7]

orImm8 :: Int -> Int -> B
orImm8 r imm = [rexW 0 0 r, 0x83, modRM 3 1 r, fromIntegral (imm .&. 0xFF)]

addImm32, subImm32 :: Int -> Int -> B
addImm32 r imm = [rexW 0 0 r, 0x81, modRM 3 0 r] ++ imm32 imm
subImm32 r imm = [rexW 0 0 r, 0x81, modRM 3 5 r] ++ imm32 imm

jccByte :: Cond -> Word8
jccByte = \case
  JEq -> 0x84
  JNe -> 0x85
  JLt -> 0x8C
  JLe -> 0x8E
  JGt -> 0x8F
  JGe -> 0x8D

data Frag = Frag B [(Int, Label)]

bytes :: B -> Frag
bytes b = Frag b []

appendFrag :: Frag -> Frag -> Frag
appendFrag (Frag a fa) (Frag b fb) =
  let n = length a
   in Frag (a ++ b) (fa ++ [(i + n, l) | (i, l) <- fb])

jccRel32 :: Word8 -> Label -> Frag
jccRel32 cc lbl = Frag [0x0F, cc, 0, 0, 0, 0] [(2, lbl)]

jmpRel32 :: Label -> Frag
jmpRel32 lbl = Frag [0xE9, 0, 0, 0, 0] [(1, lbl)]

checkFitsImmediate :: Int -> Label -> Frag
checkFitsImmediate r bailoutLbl =
  let pre = movRR 11 r ++ shl3 11 ++ sar3 11 ++ cmpRR 11 r
   in appendFrag (bytes pre) (jccRel32 0x85 bailoutLbl)

prologueBytes :: B
prologueBytes =
  [ 0x55, -- push rbp
    0x48, 0x89, 0xE5, -- mov rbp, rsp
    0x53, -- push rbx
    0x41, 0x54, -- push r12
    0x41, 0x55, -- push r13
    0x41, 0x56, -- push r14
    0x41, 0x57, -- push r15
    0x48, 0x83, 0xEC, 0x30 -- sub rsp, 48 (spill area for RBudgets, RT3..RT7)
  ]
    ++ movRR 3 7 -- rbx (RState)   = rdi
    ++ movRR 12 6 -- r12 (RArgs)    = rsi
    ++ storeRbp8 2 (-48) -- [rbp - 48] = rdx (RBudgets*)
    ++ loadImmIx 13 2 budgetDepthIdx -- r13 (RDepth) = budgets[0]
    ++ loadImmIx 14 3 stateCellsIdx
    ++ loadImmIx 15 3 stateTrailIdx
    ++ loadImmIx 8 3 stateHIdx
    ++ loadImmIx 9 3 stateTRIdx
    ++ loadImmIx 10 3 stateHBIdx

epilogueBytes :: Int64 -> B
epilogueBytes code =
  storeImmIx 8 3 stateHIdx
    ++ storeImmIx 9 3 stateTRIdx
    ++ loadRbp8 2 (-48) -- rdx = RBudgets*
    ++ storeImmIx 13 2 budgetDepthIdx -- budgets[0] = r13 (RDepth)
    ++ movImm 0 code
    ++ [ 0x48, 0x83, 0xC4, 0x30, -- add rsp, 48
         0x41, 0x5F, -- pop r15
         0x41, 0x5E, -- pop r14
         0x41, 0x5D, -- pop r13
         0x41, 0x5C, -- pop r12
         0x5B, -- pop rbx
         0x5D, -- pop rbp
         0xC3 -- ret
       ]

emitOp :: JitOp -> (Frag, Maybe Label)
emitOp = \case
  JLabel lbl -> (bytes [], Just lbl)
  JMovImm dst v ->
    case hwLoc dst of
      Left hw -> (bytes (movImm hw v), Nothing)
      Right disp -> (bytes (movImm 0 v ++ storeRbp8 0 disp), Nothing)
  JMov dst src ->
    let (s, loadS) = getReg 0 src
     in (bytes (loadS ++ putReg dst s), Nothing)
  JLoadIx dst base idx ->
    let (b, loadB) = getReg 0 base
        (i, loadI) = getReg 2 idx
     in case hwLoc dst of
          Left d -> (bytes (loadB ++ loadI ++ loadRegIx d b i), Nothing)
          Right disp -> (bytes (loadB ++ loadI ++ loadRegIx 0 b i ++ storeRbp8 0 disp), Nothing)
  JStoreIx src base idx ->
    let (s, loadS) = getReg 0 src
        (b, loadB) = getReg 2 base
        (i, loadI) = getReg 11 idx
     in (bytes (loadS ++ loadB ++ loadI ++ storeRegIx s b i), Nothing)
  JLoadImm dst base idx ->
    let (b, loadB) = getReg 0 base
     in case hwLoc dst of
          Left d -> (bytes (loadB ++ loadImmIx d b idx), Nothing)
          Right disp -> (bytes (loadB ++ loadImmIx 0 b idx ++ storeRbp8 0 disp), Nothing)
  JStoreImm src base idx ->
    let (s, loadS) = getReg 0 src
        (b, loadB) = getReg 2 base
     in (bytes (loadS ++ loadB ++ storeImmIx s b idx), Nothing)
  JTagOf dst src ->
    let (s, loadS) = getReg 0 src
     in (bytes (loadS ++ movRR 0 s ++ and7 0 ++ putReg dst 0), Nothing)
  JValOf dst src ->
    let (s, loadS) = getReg 0 src
     in (bytes (loadS ++ movRR 0 s ++ sar3 0 ++ putReg dst 0), Nothing)
  JMkWord dst val tag ->
    let (v, loadV) = getReg 0 val
     in (bytes (loadV ++ movRR 0 v ++ shl3 0 ++ (if tag == 0 then [] else orImm8 0 tag) ++ putReg dst 0), Nothing)
  JDeref dst src ->
    let (s, loadS) = getReg 0 src
        initB = loadS ++ movRR 0 s
        loopB =
          [ 0x48, 0x89, 0xC2,
            0x48, 0x83, 0xE2, 0x07,
            0x75, 0x15,
            0x48, 0x89, 0xC2,
            0x48, 0xC1, 0xFA, 0x03,
            0x4D, 0x8B, 0x1C, 0xD6,
            0x49, 0x39, 0xC3,
            0x74, 0x05,
            0x4C, 0x89, 0xD8,
            0xEB, 0xE2
          ]
     in (bytes (initB ++ loopB ++ putReg dst 0), Nothing)
  JAddChecked dst a b bailoutLbl ->
    let (ra, loadA) = getReg 0 a
        (rb, loadB) = getReg 2 b
        pre = loadA ++ loadB ++ movRR 0 ra ++ [rexW rb 0 0, 0x01, modRM 3 rb 0]
        f1 = appendFrag (bytes pre) (jccRel32 0x80 bailoutLbl)
        f2 = appendFrag f1 (checkFitsImmediate 0 bailoutLbl)
     in (appendFrag f2 (bytes (putReg dst 0)), Nothing)
  JSubChecked dst a b bailoutLbl ->
    let (ra, loadA) = getReg 0 a
        (rb, loadB) = getReg 2 b
        pre = loadA ++ loadB ++ movRR 0 ra ++ [rexW rb 0 0, 0x29, modRM 3 rb 0]
        f1 = appendFrag (bytes pre) (jccRel32 0x80 bailoutLbl)
        f2 = appendFrag f1 (checkFitsImmediate 0 bailoutLbl)
     in (appendFrag f2 (bytes (putReg dst 0)), Nothing)
  JMulChecked dst a b bailoutLbl ->
    let (ra, loadA) = getReg 0 a
        (rb, loadB) = getReg 2 b
        pre = loadA ++ loadB ++ movRR 0 ra ++ [rexW 0 0 rb, 0x0F, 0xAF, modRM 3 0 rb]
        f1 = appendFrag (bytes pre) (jccRel32 0x80 bailoutLbl)
        f2 = appendFrag f1 (checkFitsImmediate 0 bailoutLbl)
     in (appendFrag f2 (bytes (putReg dst 0)), Nothing)
  JAddImm dst src imm ->
    let (s, loadS) = getReg 0 src
     in (bytes (loadS ++ movRR 0 s ++ addImm32 0 imm ++ putReg dst 0), Nothing)
  JSubImm dst src imm ->
    let (s, loadS) = getReg 0 src
     in (bytes (loadS ++ movRR 0 s ++ subImm32 0 imm ++ putReg dst 0), Nothing)
  JTickDepth exhaustedLbl ->
    -- sub r13, 1 (49 83 ED 01); js exhaustedLbl
    (appendFrag (bytes [0x49, 0x83, 0xED, 0x01]) (jccRel32 0x88 exhaustedLbl), Nothing)
  JTickDepthReg stepReg exhaustedLbl ->
    let (rs, loadS) = getReg 0 stepReg
        -- sub r13, rs (rexW rs 0 13, 0x29, modRM 3 rs 13); js exhaustedLbl
        pre = loadS ++ [rexW rs 0 13, 0x29, modRM 3 rs 13]
     in (appendFrag (bytes pre) (jccRel32 0x88 exhaustedLbl), Nothing)
  JBindRef addrReg valReg bailoutLbl ->
    let (a, loadA) = getReg 0 addrReg
        (v, loadV) = getReg 2 valReg
        capCheck = loadImmIx 11 3 stateTrailCapIdx ++ cmpRR 9 11
        post =
          movRR 11 a
            ++ [0x49, 0xD1, 0xE3]
            ++ storeRegIx 11 15 9
            ++ [0x49, 0x83, 0xC1, 0x01]
        -- jge over the trail push: capCheck, its jcc rel32 (6 bytes) and post.
        -- Derived from the emitted bytes; a hard-coded 0x1A fell one byte
        -- short and jumped into the middle of the final add.
        skip = length capCheck + 6 + length post
        pre =
          loadA
            ++ loadV
            ++ storeRegIx v 14 a
            ++ cmpRR a 10
            ++ [0x7D, fromIntegral skip]
            ++ capCheck
     in (appendFrag (appendFrag (bytes pre) (jccRel32 0x8D bailoutLbl)) (bytes post), Nothing)
  JJump lbl -> (jmpRel32 lbl, Nothing)
  JBranchCmp c a b lbl ->
    let (ra, loadA) = getReg 0 a
        (rb, loadB) = getReg 2 b
     in (appendFrag (bytes (loadA ++ loadB ++ cmpRR ra rb)) (jccRel32 (jccByte c) lbl), Nothing)
  JBranchImm c a imm lbl ->
    let (ra, loadA) = getReg 0 a
     in (appendFrag (bytes (loadA ++ movImm 11 imm ++ cmpRR ra 11)) (jccRel32 (jccByte c) lbl), Nothing)
  JReturn code -> (bytes (epilogueBytes code), Nothing)

assembleX64 :: JitUnit -> [Word8]
assembleX64 (JitUnit ops) = patched
  where
    laid = (bytes prologueBytes, Nothing) : map emitOp ops
    offs = scanl (\acc (Frag b _, _) -> acc + length b) 0 laid
    labels = M.fromList [(lbl, off) | ((_, Just lbl), off) <- zip laid offs]
    patched = concat [patchFrag base frag | ((frag, _), base) <- zip laid offs]
    patchFrag base (Frag b fx) =
      foldl
        ( \acc (fo, lbl) ->
            let target = M.findWithDefault (error ("Infera.Core.Jit.AsmX64: unknown label " ++ lbl)) lbl labels
                rel = target - (base + fo + 4)
             in take fo acc ++ imm32 rel ++ drop (fo + 4) acc
        )
        b
        fx
