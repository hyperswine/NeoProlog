module Main (main, replay) where

import Control.Monad (unless)
import Data.String (fromString)
import Hedgehog
import InferaTest (inferaGroup)
import CorrectnessTest (correctnessGroup)
import MinesweeperTest (minesweeperGroup)
import System.Exit (exitFailure)

main :: IO ()
main = do
  ok <- checkSequential inferaGroup
  modelsOk <- checkSequential correctnessGroup
  minesOk <- checkSequential minesweeperGroup
  unless (ok && modelsOk && minesOk) exitFailure

-- Paste the property name, seed and shrink path from a failure report into
-- GHCi to reproduce precisely the minimized counterexample.
replay :: String -> Seed -> String -> IO ()
replay name seed path =
  case lookup (fromString name) (concatMap groupProperties [inferaGroup, correctnessGroup, minesweeperGroup]) of
    Nothing -> fail ("Unknown property: " ++ name)
    Just prop -> recheckAt seed (fromString path) prop
