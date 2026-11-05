{-# LANGUAGE OverloadedStrings #-}

-- The x86-64 JIT backend is only exercised natively on Linux CI, so its
-- encodings are checked here by assembling, on any host. Both checks guard
-- regressions that once crashed the Linux suite (0c0d689) and came back when
-- the backend was replaced by an older copy.
module JitEncodingTest (jitEncodingGroup, jitNativeGroup) where

import Control.Monad (forM_)
import Data.List (nub)
import Data.Int (Int64)
import Foreign.Marshal.Array (allocaArray, peekArray, pokeArray)
import Foreign.Ptr (ptrToIntPtr)
import Foreign.Storable (peekElemOff)
import Hedgehog
import Infera.Core.Jit (runNativeUnit)
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
      ("bind skips the trail push onto the cell store", bindSkip)
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

-- JBindRef jumps over the trail check and push with a short jge when the
-- bound cell is not older than the choice boundary. The jump must land
-- exactly on the cell store that ends the op, not inside an instruction and
-- not past the store.
bindSkip :: Property
bindSkip = withTests 1 . property $
  forM_ [(a, v) | a <- temps, v <- temps, a /= v] $ \(a, v) -> do
    let unit = assembleX64 (JitUnit [JBindRef a v "after", JLabel "after", JReturn 0])
        base = assembleX64 (JitUnit [JReturn 0])
        size = length unit - length base
        op = take size (drop (length prologueBytes) unit)
        -- The store is `mov [r14 + a*8], v` (REX.W 89 /r, SIB) with no displacement.
        storeLen = 4
        landsOnStore j = op !! j == 0x7D && j + 2 + fromIntegral (op !! (j + 1)) == size - storeLen
        storeAtEnd = op !! (size - storeLen + 1) == 0x89
    annotateShow (a, v, op)
    assert storeAtEnd
    assert (any landsOnStore [0 .. size - 2])
  where
    temps = [RT0, RT1, RT2, RT3, RT4, RT5, RT6, RT7]

-- Ops run natively on this host (AArch64 here, x86-64 on Linux CI).
jitNativeGroup :: Group
jitNativeGroup =
  Group
    "JIT ops run natively"
    [ ("a bind that cannot be trailed leaves the cell unwritten", bindFullTrail),
      ("a bind with trail room trails, then writes", bindTrailRoom),
      ("a bind above the choice boundary writes without trailing", bindYoung)
    ]

data BindRun = BindRun {brCode :: Maybe Int64, brCell :: Int64, brTR :: Int64, brTrail :: [Int64]}
  deriving (Show)

-- Cells 0..15 hold `untouched`; H = HB = 8, TR = 4 in an 8-entry trail
-- whose capacity is given. The unit binds cells[addr] = 99 with a and v as
-- the address and value registers.
runBind :: Reg -> Reg -> Int64 -> Int64 -> IO BindRun
runBind a v addr trailCap =
  allocaArray 16 $ \cells -> allocaArray 8 $ \trail -> allocaArray 8 $ \st ->
    allocaArray 2 $ \budgets -> allocaArray 2 $ \args -> do
      pokeArray cells (replicate 16 untouched)
      pokeArray trail (replicate 8 (-1))
      pokeArray st [fromIntegral (ptrToIntPtr cells), fromIntegral (ptrToIntPtr trail), 8, 4, 8, 16, trailCap, 0]
      pokeArray budgets [100, 100]
      pokeArray args [addr, 99]
      code <-
        runNativeUnit
          ( JitUnit
              [ JLoadImm a RArgs 0,
                JLoadImm v RArgs 1,
                JBindRef a v "bail",
                JReturn jitSuccess,
                JLabel "bail",
                JReturn jitBailout
              ]
          )
          st
          args
          budgets
      BindRun code <$> peekElemOff cells (fromIntegral addr) <*> peekElemOff st stateTRIdx <*> peekArray 8 trail

untouched :: Int64
untouched = 0x77

bindPairs :: [(Reg, Reg)]
bindPairs = [(a, v) | a <- ts, v <- ts, a /= v]
  where
    ts = [RT0, RT1, RT3, RT6, RT7]

forBind :: Int64 -> Int64 -> (BindRun -> PropertyT IO ()) -> Property
forBind addr cap expect = withTests 1 . property $
  forM_ bindPairs $ \(a, v) -> do
    r <- evalIO (runBind a v addr cap)
    annotateShow (a, v, r)
    case brCode r of
      Nothing -> pure () -- no native backend on this host
      Just _ -> expect r

bindFullTrail :: Property
bindFullTrail = forBind 3 4 $ \r -> do
  brCode r === Just jitBailout
  brCell r === untouched
  brTR r === 4

bindTrailRoom :: Property
bindTrailRoom = forBind 3 8 $ \r -> do
  brCode r === Just jitSuccess
  brCell r === 99
  brTR r === 5
  brTrail r !! 4 === 6

bindYoung :: Property
bindYoung = forBind 10 4 $ \r -> do
  brCode r === Just jitSuccess
  brCell r === 99
  brTR r === 4
