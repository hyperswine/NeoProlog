{-# LANGUAGE OverloadedStrings #-}

-- The x86-64 JIT backend is only exercised natively on Linux CI, so its
-- encodings are checked here by assembling, on any host. Both checks guard
-- regressions that once crashed the Linux suite (0c0d689) and came back when
-- the backend was replaced by an older copy.
module JitEncodingTest (jitEncodingGroup) where

import Control.Monad (forM_)
import Data.List (nub)
import Hedgehog
import Infera.Core.Jit.AsmX64 (assembleX64, hwLoc, prologueBytes)
import Infera.Core.Jit.IR

allRegs :: [Reg]
allRegs =
  [ RState, RArgs, RBudgets, RCells, RTrail, RH, RTR, RHB,
    RT0, RT1, RT2, RT3, RT4, RT5, RT6, RT7
  ]

jitEncodingGroup :: Group
jitEncodingGroup =
  Group
    "x86-64 JIT encodings"
    [ ("spill slots sit below the saved callee registers", spillSlots),
      ("bind skips exactly the trail push", bindSkip)
    ]

-- The prologue pushes rbp, then rbx and r12-r15 to [rbp-8 .. rbp-40], and
-- reserves 48 bytes below them. Every spilled register needs its own 8-byte
-- slot inside that area, or returning restores a clobbered callee register.
spillSlots :: Property
spillSlots = withTests 1 . property $ do
  let slots = [(r, off) | r <- allRegs, Right off <- [hwLoc r]]
  forM_ slots $ \(r, off) -> do
    annotateShow (r, off)
    assert (off <= -48 && off >= -88)
  length (nub (map snd slots)) === length slots

-- JBindRef jumps over the trail push with a short jge when the bound cell is
-- not older than the choice boundary. The jump must land exactly at the end
-- of the op, not inside its last instruction.
bindSkip :: Property
bindSkip = withTests 1 . property $
  forM_ [(a, v) | a <- temps, v <- temps, a /= v] $ \(a, v) -> do
    let unit = assembleX64 (JitUnit [JBindRef a v "after", JLabel "after", JReturn 0])
        base = assembleX64 (JitUnit [JReturn 0])
        size = length unit - length base
        op = take size (drop (length prologueBytes) unit)
        landsAtEnd j = op !! j == 0x7D && j + 2 + fromIntegral (op !! (j + 1)) == size
    annotateShow (a, v, op)
    assert (any landsAtEnd [0 .. size - 2])
  where
    temps = [RT0, RT1, RT2, RT3, RT4, RT5, RT6, RT7]
