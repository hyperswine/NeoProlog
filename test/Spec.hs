{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Main where

import Control.Monad (unless)
import Hedgehog
import NeoPrologTest (neoPrologGroup)
import System.Exit (exitFailure)

main :: IO ()
main = do
  ok <- checkParallel neoPrologGroup
  unless ok exitFailure
