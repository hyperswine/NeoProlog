{-# LANGUAGE LambdaCase #-}

-- | AArch64 (AAPCS64) native code emitter for the Infera JIT tier.
--
-- Adapted from fprisc:compiler/Sol/AsmA64.hs
-- Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
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
w x = [fromIntegral (x `shiftR` s .&. 0xFF) | s <- [0, 8, 16, 24 :: Int]]

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
  RT0 -> 9
  RT1 -> 10
  RT2 -> 11
  RT3 -> 12
  RT4 -> 13
  RT5 -> 14
  RT6 -> 6
  RT7 -> 7

rDepth, rScratch0, rScratch1, rScratch2 :: Int
rDepth = 27
rScratch0 = 15
rScratch1 = 16
rScratch2 = 17

movRR :: Int -> Int -> I
movRR d n = 0xAA0003E0 .|. fromIntegral (n `shiftL` 16) .|. fromIntegral d

ldrImm, strImm :: Int -> Int -> Int -> I
ldrImm t n idx = 0xF9400000 .|. fromIntegral (idx `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t
strImm t n idx = 0xF9000000 .|. fromIntegral (idx `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t

ldrIx, strIx :: Int -> Int -> Int -> I
ldrIx t n m = 0xF8607800 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t
strIx t n m = 0xF8207800 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral t

addImm, subImm :: Int -> Int -> Int -> I
addImm d n imm = 0x91000000 .|. fromIntegral (imm `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
subImm d n imm = 0xD1000000 .|. fromIntegral (imm `shiftL` 10) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

cmpImm12 :: Int -> Int -> I
cmpImm12 n imm = 0xF100001F .|. fromIntegral (imm `shiftL` 10) .|. fromIntegral (n `shiftL` 5)

addsRR, subsRR, mulRR, smulhRR :: Int -> Int -> Int -> I
addsRR d n m = 0xAB000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
subsRR d n m = 0xEB000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
mulRR d n m = 0x9B007C00 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
smulhRR d n m = 0x9B407C00 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

cmpRR :: Int -> Int -> I
cmpRR n m = subsRR 31 n m

cmpAsr63 :: Int -> Int -> I
cmpAsr63 n m = 0xEB80FC1F .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5)

lsl3, asr3 :: Int -> Int -> I
lsl3 d n = 0xD37DF000 .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d
asr3 d n = 0x9343FC00 .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

and7 :: Int -> Int -> I
and7 d n = 0x92400800 .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

orrRR :: Int -> Int -> Int -> I
orrRR d n m = 0xAA000000 .|. fromIntegral (m `shiftL` 16) .|. fromIntegral (n `shiftL` 5) .|. fromIntegral d

cbnzScratch0 :: Int -> I
cbnzScratch0 offsetWords =
  0xB5000000 .|. (fromIntegral (offsetWords .&. 0x7FFFF) `shiftL` 5) .|. fromIntegral rScratch0

bCondRel :: I -> Int -> I
bCondRel c offsetWords =
  0x54000000 .|. (fromIntegral (offsetWords .&. 0x7FFFF) `shiftL` 5) .|. c

bRel :: Int -> I
bRel offsetWords =
  0x14000000 .|. fromIntegral (offsetWords .&. 0x3FFFFFF)

movImm64 :: Int -> Int64 -> [I]
movImm64 r v =
  let u = fromIntegral v :: Integer
      hs = [(fromIntegral ((u `shiftR` (16 * k)) .&. 0xFFFF) :: I, k) | k <- [0 .. 3 :: Int]]
      movz :: (I, Int) -> I
      movz (h, k) = 0xD2800000 .|. (fromIntegral k `shiftL` 21) .|. (h `shiftL` 5) .|. fromIntegral r
      movk :: (I, Int) -> I
      movk (h, k) = 0xF2800000 .|. (fromIntegral k `shiftL` 21) .|. (h `shiftL` 5) .|. fromIntegral r
   in case hs of
        [] -> []
        (h0 : rest) -> movz h0 : [movk hk | hk@(h, _) <- rest, h /= 0]

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

bCondPlaceholder :: I -> I
bCondPlaceholder c = 0x54000000 .|. c

bUncondPlaceholder :: I
bUncondPlaceholder = 0x14000000

data Frag = Frag [I] [(Int, Label, Bool)]

ws :: [I] -> Frag
ws is = Frag is []

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

prologueWords :: [I]
prologueWords =
  [ 0xA9BF7BFD,
    addImm 29 31 0,
    0xA9BF53F3,
    0xA9BF5BF5,
    0xA9BF63F7,
    0xA9BF6BF9,
    0xA9BF73FB,
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
    ++ [ 0xA8C173FB,
         0xA8C16BF9,
         0xA8C163F7,
         0xA8C15BF5,
         0xA8C153F3,
         0xA8C17BFD,
         0xD65F03C0
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
  JMkWord dst val tag ->
    let d = hwReg dst
        v = hwReg val
     in ( ws (lsl3 d v : if tag == 0 then [] else movImm64 rScratch0 (fromIntegral tag) ++ [orrRR d d rScratch0]),
          Nothing
        )
  JDeref dst src ->
    let d = hwReg dst
        s = hwReg src
     in ( ws
            ( [movRR d s | d /= s]
                ++ [ and7 rScratch0 d,
                     cbnzScratch0 7,
                     asr3 rScratch1 d,
                     ldrIx rScratch2 (hwReg RCells) rScratch1,
                     cmpRR rScratch2 d,
                     bCondRel condEQ 3,
                     movRR d rScratch2,
                     bRel (-7)
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
  JAddImm dst src imm -> (ws [addImm (hwReg dst) (hwReg src) imm], Nothing)
  JSubImm dst src imm -> (ws [subImm (hwReg dst) (hwReg src) imm], Nothing)
  JTickDepth exhaustedLbl ->
    ( Frag
        [ 0xF1000400 .|. fromIntegral (rDepth `shiftL` 5) .|. fromIntegral rDepth,
          bCondPlaceholder condMI
        ]
        [(1, exhaustedLbl, True)],
      Nothing
    )
  JTickDepthReg stepReg exhaustedLbl ->
    ( Frag
        [ subsRR rDepth rDepth (hwReg stepReg),
          bCondPlaceholder condMI
        ]
        [(1, exhaustedLbl, True)],
      Nothing
    )
  JBindRef addrReg valReg bailoutLbl ->
    let a = hwReg addrReg
        v = hwReg valReg
     in ( Frag
            [ strIx v (hwReg RCells) a,
              cmpRR a (hwReg RHB),
              bCondRel condGE 7,
              ldrImm rScratch0 (hwReg RState) stateTrailCapIdx,
              cmpRR (hwReg RTR) rScratch0,
              bCondPlaceholder condGE,
              addImm rScratch1 31 0,
              strIx rScratch1 (hwReg RTrail) (hwReg RTR),
              addImm (hwReg RTR) (hwReg RTR) 1
            ]
            [(5, bailoutLbl, True)]
            `replaceWord6` (0xD37FF800 .|. fromIntegral (a `shiftL` 5) .|. fromIntegral rScratch1),
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
  JReturn code -> (ws (epilogueWords code), Nothing)
  where
    replaceWord6 (Frag is fx) w6 = Frag (take 6 is ++ [w6] ++ drop 7 is) fx
    _ = seqId

assembleA64 :: JitUnit -> [Word8]
assembleA64 (JitUnit ops) = concatMap w patched
  where
    laid = (ws prologueWords, Nothing) : [emitOp i op | (i, op) <- zip [0 :: Int ..] ops]
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
