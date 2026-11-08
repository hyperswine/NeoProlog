{-# LANGUAGE LambdaCase #-}

-- | AArch64 (AAPCS64) native code emitter for the Infera JIT tier.
--
-- Adapted from fprisc:compiler/Sol/AsmA64.hs
-- Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
--
-- Register mapping (AAPCS64):
--   Entry parameters: x0 = state*, x1 = args*, x2 = budgets*
--   x19 = RState    (callee-saved)
--   x20 = RArgs     (callee-saved)
--   x21 = RBudgets  (callee-saved)
--   x22 = RCells    (callee-saved)
--   x23 = RTrail    (callee-saved)
--   x24 = RH        (callee-saved)
--   x25 = RTR       (callee-saved)
--   x26 = RHB       (callee-saved)
--   x27 = RDepth    (callee-saved cached budgets[0] resolution depth budget)
--   x9  = RT0       (caller-saved working register)
--   x10 = RT1       (caller-saved working register)
--   x11 = RT2       (caller-saved working register)
--   x12 = RT3       (caller-saved working register)
--   x13 = RT4       (caller-saved working register)
--   x14 = RT5       (caller-saved working register)
--   x6  = RT6       (caller-saved working register)
--   x7  = RT7       (caller-saved working register)
--   x28 = RE        (callee-saved; native environment frame)
--   x8  = RSP       (native stack top; native code calls no C, so a
--                    caller-saved register is safe)
--   x15, x16, x17 = internal assembler scratch registers
module Infera.Core.Jit.AsmA64
  ( assembleA64,
  )
where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.Int (Int64)
import qualified Data.Map.Strict as M
import Data.Word (Word32, Word8)
import Infera.Core.Jit.IR

type I = Word32

w :: I -> [Word8]
w x = [fromIntegral (x `shiftR` s .&. 0xFF) | s <- [0, 8, 16, 24]]

hwReg :: Reg -> Int
hwReg = \case
  RState -> 19
  RArgs -> 20
  RBudgets -> 21
  RCells -> 22
  RTrail -> 23
  RH -> 24
  RTR -> 25
  RHB -> 26
  RDepth -> 27
  RT0 -> 9
  RT1 -> 10
  RT2 -> 11
  RT3 -> 12
  RT4 -> 13
  RT5 -> 14
  RT6 -> 6
  RT7 -> 7
  RE -> 28
  RSP -> 8

rDepth, rScratch0, rScratch1, rScratch2 :: Int
rDepth = 27
rScratch0 = 15
rScratch1 = 16
rScratch2 = 17

-- ─── AArch64 instruction encoders ────────────────────────────────────────────

-- mov xD, xN  (orr xD, xzr, xN)
movRR :: Int -> Int -> I
movRR d n = 0xAA0003E0 .|. fromIntegral (n `shiftL` 16) .|. fromIntegral d

-- ldr / str xT, [xN, #imm12*8]
ldrImm, strImm :: Int -> Int -> Int -> I
ldrImm t n idx = 0xF9400000 .|. fromIntegral (idx `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t
strImm t n idx = 0xF9000000 .|. fromIntegral (idx `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t

-- ldr / str xT, [xN, xM, lsl #3]
ldrIx, strIx :: Int -> Int -> Int -> I
ldrIx t n m = 0xF8607800 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t
strIx t n m = 0xF8207800 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t

-- add / sub xD, xN, #imm12
addImm, subImm :: Int -> Int -> Int -> I
addImm d n imm = 0x91000000 .|. fromIntegral (imm `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
subImm d n imm = 0xD1000000 .|. fromIntegral (imm `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- cmp xN, #imm12  (subs xzr, xN, #imm12)
cmpImm12 :: Int -> Int -> I
cmpImm12 n imm = 0xF100001F .|. fromIntegral (imm `shiftL` 10) .|. fromIntegral (n `shiftL` 5)

-- add / sub / adds / subs / mul / smulh xD, xN, xM
addsRR, subsRR, mulRR, smulhRR :: Int -> Int -> Int -> I
addsRR d n m = 0xAB000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
subsRR d n m = 0xEB000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
mulRR d n m = 0x9B007C00 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
smulhRR d n m = 0x9B407C00 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- cmp xN, xM  (subs xzr, xN, xM)
cmpRR :: Int -> Int -> I
cmpRR n m = subsRR 31 n m

-- cmp xN, xM, asr #63  (subs xzr, xN, xM, asr #63)
cmpAsr63 :: Int -> Int -> I
cmpAsr63 n m = 0xEB80FC1F .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5)

-- lsl / asr by 3 bits:
-- lsl xD, xN, #3  -> ubfm xD, xN, #61, #60
-- asr xD, xN, #3  -> sbfm xD, xN, #3, #63
lsl3, asr3 :: Int -> Int -> I
lsl3 d n = 0xD37DF000 .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
asr3 d n = 0x9343FC00 .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- and xD, xN, #7  (N=1, immr=0, imms=2 -> 0x92400800)
and7 :: Int -> Int -> I
and7 d n = 0x92400800 .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- and xD, xN, xM
andRR :: Int -> Int -> Int -> I
andRR d n m = 0x8A000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- asr xD, xN, #k  (sbfm xD, xN, #k, #63)
-- | @sdiv d, n, m@
sdivRR :: Int -> Int -> Int -> I
sdivRR d n m = 0x9AC00C00 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- | @msub d, n, m, a@: @d = a - n * m@
msubRRR :: Int -> Int -> Int -> Int -> I
msubRRR d n m a = 0x9B008000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (a `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- | @eor d, n, m@
eorRR :: Int -> Int -> Int -> I
eorRR d n m = 0xCA000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- | @add d, n, m@
addRR :: Int -> Int -> Int -> I
addRR d n m = 0x8B000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

asrImm :: Int -> Int -> Int -> I
asrImm d n k = 0x9340FC00 .|. fromIntegral (k `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

-- orr xD, xN, xM
orrRR :: Int -> Int -> Int -> I
orrRR d n m = 0xAA000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

movImm64 :: Int -> Int64 -> [I]
movImm64 r v =
  let u = fromIntegral v :: Integer
      hs = [(fromIntegral ((u `shiftR` (16 * k)) .&. 0xFFFF) :: I, k) | k <- [0 .. 3]]
      movz (h, k) = 0xD2800000 .|. (fromIntegral k `shiftL` 21) .|. (h `shiftL` 5) .|. fromIntegral r
      movk (h, k) = 0xF2800000 .|. (fromIntegral k `shiftL` 21) .|. (h `shiftL` 5) .|. fromIntegral r
   in case hs of
        [] -> []
        (h0 : rest) -> movz h0 : [movk hk | hk@(h, _) <- rest, h /= 0]

-- Condition codes for B.cond:
condEQ, condNE, condMI, condVS, condGE, condLT, condGT, condLE :: I
condEQ = 0x0
condNE = 0x1
condMI = 0x4
condVS = 0x6
condGE = 0xA
condLT = 0xB
condGT = 0xC
condLE = 0xD

a64Cond :: Cond -> I
a64Cond = \case
  JEq -> condEQ
  JNe -> condNE
  JLt -> condLT
  JLe -> condLE
  JGt -> condGT
  JGe -> condGE

-- B.cond offset (imm19 in bits 23..5)
bCondPlaceholder :: I -> I
bCondPlaceholder c = 0x54000000 .|. c

-- Unconditional B offset (imm26 in bits 25..0)
bUncondPlaceholder :: I
bUncondPlaceholder = 0x14000000

-- Fixup: (word offset inside fragment, target label, isCondBranch)
data Frag = Frag [I] [(Int, Label, Bool)]

ws :: [I] -> Frag
ws is = Frag is []

-- Check that value in register `rd` fits in 61-bit signed immediate:
-- lsl xScratch0, xRd, #3; asr xScratch0, xScratch0, #3; cmp xScratch0, xRd; b.ne bailoutLbl
checkFitsImmediate :: Int -> Label -> Frag
checkFitsImmediate rd bailoutLbl =
  Frag
    [ lsl3 rScratch0 rd,
      asr3 rScratch0 rScratch0,
      cmpRR rScratch0 rd,
      bCondPlaceholder condNE
    ]
    [(3, bailoutLbl, True)]

appendFrag :: Frag -> Frag -> Frag
appendFrag (Frag a fa) (Frag b fb) =
  let n = length a
   in Frag (a ++ b) (fa ++ [(i + n, l, c) | (i, l, c) <- fb])

-- Save callee-saved x19..x28 and load RState..RHB + RDepth from x0..x2
prologueWords :: [I]
prologueWords =
  [ 0xA9BF7BFD, -- stp x29, x30, [sp, #-16]!
    addImm 29 31 0, -- mov x29, sp
    0xA9BF53F3, -- stp x19, x20, [sp, #-16]!
    0xA9BF5BF5, -- stp x21, x22, [sp, #-16]!
    0xA9BF63F7, -- stp x23, x24, [sp, #-16]!
    0xA9BF6BF9, -- stp x25, x26, [sp, #-16]!
    0xA9BF73FB, -- stp x27, x28, [sp, #-16]!
    movRR (hwReg RState) 0,
    movRR (hwReg RArgs) 1,
    movRR (hwReg RBudgets) 2,
    ldrImm (hwReg RCells) (hwReg RState) stateCellsIdx,
    ldrImm (hwReg RTrail) (hwReg RState) stateTrailIdx,
    ldrImm (hwReg RH) (hwReg RState) stateHIdx,
    ldrImm (hwReg RTR) (hwReg RState) stateTRIdx,
    ldrImm (hwReg RHB) (hwReg RState) stateHBIdx,
    ldrImm rDepth (hwReg RBudgets) budgetDepthIdx
  ]

epilogueWords :: Int64 -> [I]
epilogueWords code =
  [ strImm (hwReg RH) (hwReg RState) stateHIdx,
    strImm (hwReg RTR) (hwReg RState) stateTRIdx,
    strImm rDepth (hwReg RBudgets) budgetDepthIdx
  ]
    ++ movImm64 0 code
    ++ [ 0xA8C173FB, -- ldp x27, x28, [sp], #16
         0xA8C16BF9, -- ldp x25, x26, [sp], #16
         0xA8C163F7, -- ldp x23, x24, [sp], #16
         0xA8C15BF5, -- ldp x21, x22, [sp], #16
         0xA8C153F3, -- ldp x19, x20, [sp], #16
         0xA8C17BFD, -- ldp x29, x30, [sp], #16
         0xD65F03C0 -- ret
       ]

emitOp :: Int -> JitOp -> (Frag, Maybe Label)
emitOp seqId = \case
  JLabel lbl -> (ws [], Just lbl)
  JMovImm dst v -> (ws (movImm64 (hwReg dst) v), Nothing)
  JMov dst src -> (ws [movRR (hwReg dst) (hwReg src)], Nothing)
  JLoadIx dst base idx -> (ws [ldrIx (hwReg dst) (hwReg base) (hwReg idx)], Nothing)
  JStoreIx src base idx -> (ws [strIx (hwReg src) (hwReg base) (hwReg idx)], Nothing)
  JLoadImm dst base idx -> (ws [ldrImm (hwReg dst) (hwReg base) idx], Nothing)
  JStoreImm src base idx -> (ws [strImm (hwReg src) (hwReg base) idx], Nothing)
  JTagOf dst src -> (ws [and7 (hwReg dst) (hwReg src)], Nothing)
  JValOf dst src -> (ws [asr3 (hwReg dst) (hwReg src)], Nothing)
  JAnd dst a b -> (ws [andRR (hwReg dst) (hwReg a) (hwReg b)], Nothing)
  JShr dst src k -> (ws [asrImm (hwReg dst) (hwReg src) k], Nothing)
  JMkWord dst val tag ->
    let d = hwReg dst
        v = hwReg val
     in ( ws (lsl3 d v : if tag == 0 then [] else movImm64 rScratch0 (fromIntegral tag) ++ [orrRR d d rScratch0]),
          Nothing
        )
  JDeref dst src ->
    let d = hwReg dst
        s = hwReg src
        cbnzScratch0 :: Int -> I
        cbnzScratch0 offsetWords = 0xB5000000 .|. (fromIntegral (offsetWords .&. 0x7FFFF) `shiftL` 5) .|. fromIntegral rScratch0
        bCondRel :: I -> Int -> I
        bCondRel c offsetWords = 0x54000000 .|. (fromIntegral (offsetWords .&. 0x7FFFF) `shiftL` 5) .|. c
        bRel :: Int -> I
        bRel offsetWords = 0x14000000 .|. fromIntegral (offsetWords .&. 0x3FFFFFF)
     in ( ws
            ( [movRR d s | d /= s]
                ++ [ and7 rScratch0 d, -- 0
                     cbnzScratch0 7, -- 1 -> jumps to word 8 (done)
                     asr3 rScratch1 d, -- 2
                     ldrIx rScratch2 (hwReg RCells) rScratch1, -- 3
                     cmpRR rScratch2 d, -- 4
                     bCondRel condEQ 3, -- 5 -> jumps to word 8 (done)
                     movRR d rScratch2, -- 6
                     bRel (-7) -- 7 -> jumps back to word 0 (loop)
                   ]
            ),
          Nothing
        )
  JAddChecked dst a b bailoutLbl ->
    let d = hwReg dst
        f1 = Frag [addsRR d (hwReg a) (hwReg b), bCondPlaceholder condVS] [(1, bailoutLbl, True)]
     in (appendFrag f1 (checkFitsImmediate d bailoutLbl), Nothing)
  JSubChecked dst a b bailoutLbl ->
    let d = hwReg dst
        f1 = Frag [subsRR d (hwReg a) (hwReg b), bCondPlaceholder condVS] [(1, bailoutLbl, True)]
     in (appendFrag f1 (checkFitsImmediate d bailoutLbl), Nothing)
  JMulChecked dst a b bailoutLbl ->
    let d = hwReg dst
        ra = hwReg a
        rb = hwReg b
        f1 =
          Frag
            [ mulRR rScratch1 ra rb,
              smulhRR rScratch2 ra rb,
              cmpAsr63 rScratch2 rScratch1,
              bCondPlaceholder condNE,
              movRR d rScratch1
            ]
            [(3, bailoutLbl, True)]
     in (appendFrag f1 (checkFitsImmediate d bailoutLbl), Nothing)
  JModChecked dst a b bailoutLbl ->
    -- Truncated remainder, then moved toward the divisor's sign when the
    -- two signs differ, as Haskell's 'mod'.
    let ra = hwReg a
        rb = hwReg b
        bCondRel :: I -> Int -> I
        bCondRel c offsetWords = 0x54000000 .|. (fromIntegral (offsetWords .&. 0x7FFFF) `shiftL` 5) .|. c
     in ( Frag
            [ cmpImm12 rb 0, -- 0
              bCondPlaceholder condEQ, -- 1 -> bailout
              sdivRR rScratch1 ra rb, -- 2
              msubRRR rScratch1 rScratch1 rb ra, -- 3
              cmpImm12 rScratch1 0, -- 4
              bCondRel condEQ 5, -- 5 -> word 10
              eorRR rScratch2 rScratch1 rb, -- 6
              cmpImm12 rScratch2 0, -- 7
              bCondRel condGE 2, -- 8 -> word 10
              addRR rScratch1 rScratch1 rb, -- 9
              movRR (hwReg dst) rScratch1 -- 10
            ]
            [(1, bailoutLbl, True)],
          Nothing
        )
  JAddImm dst src imm -> (ws [addImm (hwReg dst) (hwReg src) imm], Nothing)
  JSubImm dst src imm -> (ws [subImm (hwReg dst) (hwReg src) imm], Nothing)
  JTickDepth exhaustedLbl ->
    -- subs rDepth, rDepth, #1
    -- b.mi exhaustedLbl
    ( Frag
        [ 0xF1000400 .|. fromIntegral (rDepth `shiftL` 5) .|. fromIntegral rDepth,
          bCondPlaceholder condMI
        ]
        [(1, exhaustedLbl, True)],
      Nothing
    )
  JTickDepthReg stepReg exhaustedLbl ->
    -- subs rDepth, rDepth, stepReg
    -- b.mi exhaustedLbl
    ( Frag
        [ subsRR rDepth rDepth (hwReg stepReg),
          bCondPlaceholder condMI
        ]
        [(1, exhaustedLbl, True)],
      Nothing
    )
  JBindRef addrReg valReg bailoutLbl ->
    -- The cell is written last: a bailout on a full trail must leave it
    -- untouched, since the caller's unwind only undoes trailed bindings.
    let a = hwReg addrReg
        v = hwReg valReg
        bCondRel :: I -> Int -> I
        bCondRel c offsetWords = 0x54000000 .|. (fromIntegral (offsetWords .&. 0x7FFFF) `shiftL` 5) .|. c
     in ( Frag
            [ cmpRR a (hwReg RHB), -- 0: cmp addr, RHB
              bCondRel condGE 7, -- 1: if addr >= RHB, skip trailing (to word 8)
              ldrImm rScratch0 (hwReg RState) stateTrailCapIdx, -- 2: trailCap
              cmpRR (hwReg RTR) rScratch0, -- 3: cmp RTR, trailCap
              bCondPlaceholder condGE, -- 4: if RTR >= trailCap -> bailoutLbl
              0xD37FF800 .|. fromIntegral (a `shiftL` 5) .|. fromIntegral rScratch1, -- 5: lsl scratch1, addr, #1
              strIx rScratch1 (hwReg RTrail) (hwReg RTR), -- 6: RTrail[RTR] = 2 * addr
              addImm (hwReg RTR) (hwReg RTR) 1, -- 7: RTR += 1
              strIx v (hwReg RCells) a -- 8: RCells[addr] = val
            ]
            [(4, bailoutLbl, True)],
          Nothing
        )
  JJump lbl -> (Frag [bUncondPlaceholder] [(0, lbl, False)], Nothing)
  JBranchCmp c a b lbl ->
    (Frag [cmpRR (hwReg a) (hwReg b), bCondPlaceholder (a64Cond c)] [(1, lbl, True)], Nothing)
  JBranchImm c a imm lbl
    | imm >= 0 && imm < 4096 ->
        (Frag [cmpImm12 (hwReg a) (fromIntegral imm), bCondPlaceholder (a64Cond c)] [(1, lbl, True)], Nothing)
    | otherwise ->
        let ld = movImm64 rScratch0 imm
            n = length ld
         in (Frag (ld ++ [cmpRR (hwReg a) rScratch0, bCondPlaceholder (a64Cond c)]) [(n + 1, lbl, True)], Nothing)
  -- adr xD, label: the byte offset is a word delta, so immlo is zero and
  -- immhi takes the same 19-bit field position as a conditional branch.
  JLoadLabel dst lbl -> (Frag [0x10000000 .|. fromIntegral (hwReg dst)] [(0, lbl, True)], Nothing)
  -- br xN
  JJumpReg r -> (ws [0xD61F0000 .|. fromIntegral (hwReg r `shiftL` 5)], Nothing)
  JReturn code -> (ws (epilogueWords code), Nothing)
  where
    _ = seqId

assembleA64 :: JitUnit -> [Word8]
assembleA64 (JitUnit ops) = concatMap w patched
  where
    laid = (ws prologueWords, Nothing) : [emitOp i op | (i, op) <- zip [0 ..] ops]
    offs = scanl (\acc (Frag is _, _) -> acc + length is) 0 laid
    labels = M.fromList [(lbl, off) | ((_, Just lbl), off) <- zip laid offs]
    patched = concat [patchFrag base frag | ((frag, _), base) <- zip laid offs]
    patchFrag base (Frag is fx) =
      foldl
        ( \acc (wo, lbl, isCond) ->
            let target = M.findWithDefault (error ("Infera.Core.Jit.AsmA64: unknown label " ++ lbl)) lbl labels
                delta = target - (base + wo)
                enc =
                  if isCond
                    then fromIntegral (delta .&. 0x7FFFF) `shiftL` 5
                    else fromIntegral (delta .&. 0x3FFFFFF)
             in take wo acc ++ [acc !! wo .|. enc] ++ drop (wo + 1) acc
        )
        is
        fx
