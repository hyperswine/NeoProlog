module Main (main) where

import Control.Monad (unless)
import Hedgehog
import InferaTest (inferaGroup)
import System.Exit (exitFailure)

main :: IO ()
main = do
  ok <- checkSequential inferaGroup
  unless ok exitFailure
