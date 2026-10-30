-- | Kernel IR for the Infera native JIT tier.
--
-- Adapted from fprisc:compiler/Sol/KIR.hs
-- Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
--
-- Native predicate calling convention:
--
-- > int64_t pred(int64_t *state, int64_t *args, int64_t *budgets)
--
-- where:
--
-- * @state[0]@ = @cells@ base pointer (@int64_t *@)
-- * @state[1]@ = @trail@ base pointer (@int64_t *@)
-- * @state[2]@ = @rH@ (heap top, updated on return)
-- * @state[3]@ = @rTR@ (trail top, updated on return)
-- * @state[4]@ = @rHB@ (choice heap boundary)
-- * @state[5]@ = @rCAP@ (effective cells capacity / GC limit)
-- * @state[6]@ = @rTRAILCAP@ (trail capacity)
-- * @state[7]@ = @rCLP@ (active constraint store flag; non-zero declines)
--
-- * @args[0 .. arity-1]@ = call argument words
--
-- * @budgets[0]@ = remaining resolution depth budget (decremented by 1 per
--   resolution step; exhausting it returns @3 = jitExhausted@)
-- * @budgets[1]@ = remaining allocation budget (decremented by cells allocated;
--   exhausting it returns @4 = jitBailout@)
--
-- Return codes:
--
-- * @1@ = success (@jitSuccess@)
-- * @0@ = failure (@jitFailure@)
-- * @2@ = declined pre-flight (@jitDeclined@, before any trail/heap write)
-- * @3@ = resolution depth exhausted (@jitExhausted@)
-- * @4@ = mid-span bailout (@jitBailout@; driver unwinds to entry marks)
-- * @5@ = error pending (@jitError@)
module Infera.Core.Jit.IR
  ( Label,
    Reg (..),
    Cond (..),
    JitOp (..),
    JitUnit (..),
    jitFailure,
    jitSuccess,
    jitDeclined,
    jitExhausted,
    jitBailout,
    jitError,
    stateCellsIdx,
    stateTrailIdx,
    stateHIdx,
    stateTRIdx,
    stateHBIdx,
    stateCapIdx,
    stateTrailCapIdx,
    stateClpIdx,
    budgetDepthIdx,
    budgetAllocIdx,
  )
where

import Data.Int (Int64)

type Label = String

jitFailure, jitSuccess, jitDeclined, jitExhausted, jitBailout, jitError :: Int64
jitFailure = 0
jitSuccess = 1
jitDeclined = 2
jitExhausted = 3
jitBailout = 4
jitError = 5

stateCellsIdx, stateTrailIdx, stateHIdx, stateTRIdx, stateHBIdx, stateCapIdx, stateTrailCapIdx, stateClpIdx :: Int
stateCellsIdx = 0
stateTrailIdx = 1
stateHIdx = 2
stateTRIdx = 3
stateHBIdx = 4
stateCapIdx = 5
stateTrailCapIdx = 6
stateClpIdx = 7

budgetDepthIdx, budgetAllocIdx :: Int
budgetDepthIdx = 0
budgetAllocIdx = 1

-- | Virtual registers mapped to callee-saved / scratch hardware registers
-- by both A64 and X64 backends:
--
-- * 'RState'   : @state@ pointer (entry arg 0)
-- * 'RArgs'    : @args@ pointer (entry arg 1)
-- * 'RBudgets' : @budgets@ pointer (entry arg 2)
-- * 'RCells'   : cached @cells@ base pointer
-- * 'RTrail'   : cached @trail@ base pointer
-- * 'RH'       : cached heap top @rH@
-- * 'RTR'      : cached trail top @rTR@
-- * 'RHB'      : cached choice boundary @rHB@
-- * 'RT0'..'RT7': general 64-bit working registers for loop variables and scratch
data Reg
  = RState
  | RArgs
  | RBudgets
  | RCells
  | RTrail
  | RH
  | RTR
  | RHB
  | RT0
  | RT1
  | RT2
  | RT3
  | RT4
  | RT5
  | RT6
  | RT7
  deriving (Eq, Ord, Show)

data Cond
  = JEq
  | JNe
  | JLt
  | JLe
  | JGt
  | JGe
  deriving (Eq, Show)

-- | Register-level IR instructions shared by the AArch64 and x86-64 emitters.
data JitOp
  = JLabel Label
  | JMovImm Reg Int64
  | JMov Reg Reg
  | -- | @JLoadIx dst base idx@: @dst = base[idx]@ (8-byte word index)
    JLoadIx Reg Reg Reg
  | -- | @JStoreIx src base idx@: @base[idx] = src@ (8-byte word index)
    JStoreIx Reg Reg Reg
  | -- | @JLoadImm dst base idx@: @dst = base[idx]@ (small constant word index 0..15)
    JLoadImm Reg Reg Int
  | -- | @JStoreImm src base idx@: @base[idx] = src@ (small constant word index 0..15)
    JStoreImm Reg Reg Int
  | -- | @JDeref dst src@: chase @REF@ chain (@tag == 0@) in @RCells@ until non-@REF@ or self-ref
    JDeref Reg Reg
  | -- | @JTagOf dst src@: @dst = src .&. 7@
    JTagOf Reg Reg
  | -- | @JValOf dst src@: @dst = src `shiftR` 3@ (arithmetic shift right by 3)
    JValOf Reg Reg
  | -- | @JMkWord dst val tag@: @dst = (val `shiftL` 3) .|. tag@
    JMkWord Reg Reg Int
  | -- | @JAddChecked dst a b bailoutLbl@: @dst = a + b@; jump to @bailoutLbl@ if outside 61-bit immediate range
    JAddChecked Reg Reg Reg Label
  | -- | @JSubChecked dst a b bailoutLbl@: @dst = a - b@; jump to @bailoutLbl@ if outside 61-bit immediate range
    JSubChecked Reg Reg Reg Label
  | -- | @JMulChecked dst a b bailoutLbl@: @dst = a * b@; jump to @bailoutLbl@ on 64-bit or 61-bit overflow
    JMulChecked Reg Reg Reg Label
  | -- | @JAddImm dst src imm@: @dst = src + imm@ (unboxed counter/address step, small imm >= 0)
    JAddImm Reg Reg Int
  | -- | @JSubImm dst src imm@: @dst = src - imm@ (unboxed counter/address step, small imm >= 0)
    JSubImm Reg Reg Int
  | -- | @JTickDepth exhaustedLbl@: decrement @RDepth@ by 1; if @< 0@, jump to @exhaustedLbl@
    JTickDepth Label
  | -- | @JTickDepthReg stepReg exhaustedLbl@: subtract @stepReg@ from @RDepth@; if @< 0@, jump to @exhaustedLbl@
    JTickDepthReg Reg Label
  | -- | @JBindRef addrReg valReg bailoutLbl@: bind @RCells[addrReg] = valReg@ and trail if @addrReg < RHB@
    JBindRef Reg Reg Label
  | -- | @JJump label@
    JJump Label
  | -- | @JBranchCmp cond a b label@: signed 64-bit comparison of @a@ and @b@
    JBranchCmp Cond Reg Reg Label
  | -- | @JBranchImm cond a imm label@: signed 64-bit comparison of @a@ with @imm@
    JBranchImm Cond Reg Int64 Label
  | -- | @JReturn code@: write back @RH@, @RTR@, and @RDepth@ to @RState@/@RBudgets@ and return @code@
    JReturn Int64
  deriving (Eq, Show)

newtype JitUnit = JitUnit [JitOp]
  deriving (Eq, Show)
