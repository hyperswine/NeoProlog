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
import System.Exit (exitFailure)

main :: IO ()
main = do
  ok <- checkSequential inferaGroup
  modelsOk <- checkSequential correctnessGroup
  minesOk <- checkSequential minesweeperGroup
  inferenceOk <- checkSequential inferenceGroup
  clpOk <- checkSequential clpPerformanceGroup
  breadboardOk <- checkSequential breadboardGroup
  tablingOk <- checkSequential tablingGroup
  heapOk <- checkSequential machineHeapGroup
  unless (ok && modelsOk && minesOk && inferenceOk && clpOk && breadboardOk && tablingOk && heapOk) exitFailure

-- Paste the property name, seed and shrink path from a failure report into
-- GHCi to reproduce precisely the minimized counterexample.
replay :: String -> Seed -> String -> IO ()
replay name seed path =
  case lookup (fromString name) (concatMap groupProperties [inferaGroup, correctnessGroup, minesweeperGroup, inferenceGroup, clpPerformanceGroup, breadboardGroup, tablingGroup, machineHeapGroup]) of
    Nothing -> fail ("Unknown property: " ++ name)
    Just prop -> recheckAt seed (fromString path) prop
