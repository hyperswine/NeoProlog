-- | Kernel IR for the Infera native JIT tier.
--
-- Adapted from fprisc:compiler/Sol/KIR.hs
-- Copyright (c) 2026 Jasen Qin (hyperswine), MIT License.
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

data JitOp
  = JLabel Label
  | JMovImm Reg Int64
  | JMov Reg Reg
  | JLoadIx Reg Reg Reg
  | JStoreIx Reg Reg Reg
  | JLoadImm Reg Reg Int
  | JStoreImm Reg Reg Int
  | JDeref Reg Reg
  | JTagOf Reg Reg
  | JValOf Reg Reg
  | JMkWord Reg Reg Int
  | JAddChecked Reg Reg Reg Label
  | JSubChecked Reg Reg Reg Label
  | JMulChecked Reg Reg Reg Label
  | JAddImm Reg Reg Int
  | JSubImm Reg Reg Int
  | JTickDepth Label
  | JTickDepthReg Reg Label
  | JBindRef Reg Reg Label
  | JJump Label
  | JBranchCmp Cond Reg Reg Label
  | JBranchImm Cond Reg Int64 Label
  | JReturn Int64
  deriving (Eq, Show)

newtype JitUnit = JitUnit [JitOp]
  deriving (Eq, Show)
