-- Parity and timing runner for the core engine.
--
--   core-engine parity FILE...            every inline query: core vs reference vs machine
--   core-engine time FILE "query?" [N]    time N runs (default 3) on core, machine and reference
--   core-engine time --core FILE "query?" [N]   core only
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_, unless, when)
import Data.List (intercalate)
import GHC.Clock (getMonotonicTimeNSec)
import Infera hiding (main, solveQuery)
import qualified Infera.Core as Core
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush, hPutStrLn, stderr, stdout)
import Text.Printf (printf)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("parity" : files) -> do
      results <- mapM parityFile files
      let failures = sum results
      if failures == 0 then putStrLn "parity: all queries agree" else do
        hPutStrLn stderr ("parity: " ++ show failures ++ " disagreement(s)")
        exitFailure
    ["time", file, query] -> timeFile False file query 3
    ["time", file, query, runs] -> timeFile False file query (read runs)
    ["time", "--core", file, query] -> timeFile True file query 3
    ["time", "--core", file, query, runs] -> timeFile True file query (read runs)
    _ -> hPutStrLn stderr "usage: core-engine parity FILE... | core-engine time [--core] FILE \"query?\" [RUNS]" >> exitFailure

-- | The observable result of a query: rendered answers with their output,
-- the distinct errors, and the exhaustion flag.
data Observed = Observed [String] [String] Bool deriving (Eq, Show)

observe :: Query -> Search -> Observed
observe query items =
  let summary = summarizeSearch query items
   in Observed
        [showAnswer a ++ outputOf a | a <- summaryAnswers summary]
        (map showSolveError (summaryErrors summary))
        (summaryExhausted summary)
  where
    outputOf a = case answerOutput a of
      [] -> ""
      events -> " | output: " ++ show (concatMap renderOutputEvent (reverse events))

parityFile :: FilePath -> IO Int
parityFile file = do
  loaded <- loadFile file
  case loaded of
    Left err -> hPutStrLn stderr (file ++ ": " ++ err) >> pure 1
    Right (program, queries) -> do
      counts <- forM queries $ \query -> do
        let reference = observe query (Reference.solveQuery program query)
            machine = observe query (Machine.solveQuery program query)
            core = fmap (observe query) (Core.solveQuery program query)
            shown = intercalate ", " (map show (queryGoals query))
        case core of
          Nothing -> putStrLn ("  skip (" ++ maybe "?" id (Core.coreSupports program query) ++ "): " ++ shown) >> pure 0
          Just observed -> do
            let okReference = observed == reference
                okMachine = observed == machine
            if okReference && okMachine
              then putStrLn ("  ok   " ++ shown) >> pure 0
              else do
                putStrLn ("  FAIL " ++ shown)
                unless okReference $ do
                  putStrLn ("    reference: " ++ show reference)
                  putStrLn ("    core:      " ++ show observed)
                unless okMachine $ putStrLn ("    machine:   " ++ show machine)
                pure 1
      putStrLn (file ++ ": " ++ show (length queries) ++ " queries")
      pure (sum counts)

timeFile :: Bool -> FilePath -> String -> Int -> IO ()
timeFile coreOnly file queryText runs = do
  loaded <- loadFile file
  case loaded of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right (program, _) -> case parseQuery queryText of
      Left err -> hPutStrLn stderr err >> exitFailure
      Right query -> do
        let engines =
              [("core", \p q -> maybe (error ("outside the core subset: " ++ maybe "?" id (Core.coreSupports p q))) id (Core.solveQuery p q))]
                ++ (if coreOnly then [] else [("machine", Machine.solveQuery), ("reference", Reference.solveQuery)])
        forM_ engines $ \(name, solve) -> do
          forM_ [1 .. runs] $ \i -> do
            -- Re-parse per run so that the lazy result is not shared.
            fresh <- either (\e -> hPutStrLn stderr e >> exitFailure) pure (parseQuery queryText)
            cpu0 <- getCPUTime
            wall0 <- getMonotonicTimeNSec
            let observed = observe fresh (solve program fresh)
            _ <- evaluate (length (show observed))
            wall1 <- getMonotonicTimeNSec
            cpu1 <- getCPUTime
            let Observed answers errors exhausted = observed
            printf "%-9s run %d: %.3f s wall, %.3f s cpu, %d answer(s)%s%s\n" name (i :: Int)
              (fromIntegral (wall1 - wall0) / 1e9 :: Double)
              (fromIntegral (cpu1 - cpu0) / 1e12 :: Double)
              (length answers)
              (if null errors then "" else ", errors: " ++ intercalate "; " errors)
              (if exhausted then ", exhausted" else "")
            when (i == 1) $ forM_ (take 1 answers) $ \a -> putStrLn ("          " ++ take 120 a)
            hFlush stdout
