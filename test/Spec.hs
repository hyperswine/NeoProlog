module Main (main, replay) where

import Control.Monad (unless)
import Data.String (fromString)
import Hedgehog
import InferaTest (inferaGroup)
import CorrectnessTest (correctnessGroup)
import MinesweeperTest (minesweeperGroup)
import InferenceTest (inferenceGroup)
import CLPPerformanceTest (clpPerformanceGroup)
import BreadboardTest (breadboardGroup)
import TablingTest (tablingGroup)
import MachineHeapTest (machineHeapGroup)
import MachineControlTest (machineControlGroup)
import MachineSubsearchTest (machineSubsearchGroup)
import MachineCLPTest (machineCLPGroup)
import MachineBreadboardTest (machineBreadboardGroup)
import MachineTailTest (machineTailGroup)
import MachineReclaimTest (machineReclaimGroup)
import PerformanceDiagnosticTest (performanceDiagnosticGroup)
import MachineStructuredTailTest (machineStructuredTailGroup)
import MachineBuiltinTest (machineBuiltinGroup)
import MachineTableTest (machineTableGroup)
import MachineSnapshotTest (machineSnapshotGroup)
import MachineGeneralTailTest (machineGeneralTailGroup)
import MachineTailProofTest (machineTailProofGroup)
import MachineTraceTest (machineTraceGroup)
import MachineGraphReuseTest (machineGraphReuseGroup)
import MachineEnvironmentTest (machineEnvironmentGroup)
import MachineGeneralReclaimTest (machineGeneralReclaimGroup)
import MachineInternalTailTest (machineInternalTailGroup)
import MachineNormalizeTest (machineNormalizeGroup)
import CompileTest (compileGroup)
import MachineBytecodeTest (machineBytecodeGroup)
import MachineBytecodeHeapTest (machineBytecodeHeapGroup)
import System.Environment (getArgs)
import Data.List (isPrefixOf)
import System.Exit (exitFailure)

groups :: [(String, Group)]
groups =
  [ ("core", inferaGroup), ("models", correctnessGroup), ("mines", minesweeperGroup),
    ("inference", inferenceGroup), ("clp", clpPerformanceGroup), ("breadboard", breadboardGroup),
    ("tabling", tablingGroup), ("machine-heap", machineHeapGroup),
    ("machine-control", machineControlGroup), ("machine-subsearch", machineSubsearchGroup),
    ("machine-clp", machineCLPGroup), ("machine-breadboard", machineBreadboardGroup),
    ("machine-tail", machineTailGroup), ("machine-reclaim", machineReclaimGroup),
    ("diagnostics", performanceDiagnosticGroup), ("machine-structured", machineStructuredTailGroup),
    ("machine-builtins", machineBuiltinGroup), ("machine-tables", machineTableGroup),
    ("machine-snapshots", machineSnapshotGroup), ("machine-general-tail", machineGeneralTailGroup),
    ("machine-tail-proof", machineTailProofGroup), ("machine-trace", machineTraceGroup),
    ("machine-graph-reuse", machineGraphReuseGroup), ("machine-environment", machineEnvironmentGroup),
    ("machine-general-reclaim", machineGeneralReclaimGroup),
    ("machine-internal-tail", machineInternalTailGroup),
    ("machine-normalize", machineNormalizeGroup),
    ("compile", compileGroup),
    ("machine-bytecode", machineBytecodeGroup),
    ("machine-bytecode-heap", machineBytecodeHeapGroup)
  ]

main :: IO ()
main = do
  arguments <- getArgs
  selected <- case arguments of
    [] -> pure groups
    ["--group", prefix] | not (null prefix), let matches = filter (isPrefixOf prefix . fst) groups,
      not (null matches) -> pure matches
    _ -> fail "Usage: infera-test [--group NAME_PREFIX]"
  results <- mapM (checkSequential . snd) selected
  unless (and results) exitFailure

-- Paste the property name, seed and shrink path from a failure report into
-- GHCi to reproduce precisely the minimized counterexample.
replay :: String -> Seed -> String -> IO ()
replay name seed path =
  case lookup (fromString name) (concatMap (groupProperties . snd) groups) of
    Nothing -> fail ("Unknown property: " ++ name)
    Just prop -> recheckAt seed (fromString path) prop
