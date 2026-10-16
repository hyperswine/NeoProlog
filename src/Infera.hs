-- | Infera v2: a Prolog-inspired logic language with sorts, modes,
-- determinism, indexing, tabling and CLP(Z).
--
-- This module re-exports the public surface and provides 'main'.
module Infera
  ( module Infera.Syntax,
    module Infera.Error,
    module Infera.Diagnostic,
    module Infera.Unify,
    module Infera.Arith,
    module Infera.CLP,
    module Infera.Program,
    module Infera.Purity,
    module Infera.Infer,
    module Infera.Engine,
    module Infera.Module,
    module Infera.Repl,
    main,
  )
where

import Infera.Arith
import Infera.CLP
import Infera.Engine
import Infera.Error
import Infera.Diagnostic
import Infera.Infer
import Infera.Module
import Infera.Program
import Infera.Purity
import Infera.Repl
import Infera.Syntax
import Infera.Unify
import qualified Control.Exception as CE
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("reg" : paths) -> mapM_ registerModule paths
    ["--trace", file] -> runTraceFile file Nothing
    ["--trace", file, query] -> runTraceFile file (Just query)
    ("--trace" : _) -> hPutStrLn stderr "Usage: infera --trace FILE [\"query?\"]" >> exitFailure
    ("check" : "--json" : "--stdin" : path : buffers) -> checkBuffer True path buffers
    ("check" : "--stdin" : path : buffers) -> checkBuffer False path buffers
    ["check", "--json", "--stdin"] -> checkUsage
    ["check", "--stdin"] -> checkUsage
    ("check" : "--json" : paths) -> checkFiles True paths
    ("check" : paths) -> checkFiles False paths
    _ -> runRepl

-- | @infera check FILE...@: load each file (resolving imports and running the
-- checks) and report located diagnostics. Exits non-zero on errors.
checkFiles :: Bool -> [FilePath] -> IO ()
checkFiles json paths
  | null paths = checkUsage
  | otherwise = do
      diagnostics <- concat <$> mapM checkFile paths
      reportDiagnostics json paths diagnostics

-- | Read the active buffer from stdin and optional dependency snapshots from
-- temporary files. Snapshot paths never replace source identities in reports.
checkBuffer :: Bool -> FilePath -> [String] -> IO ()
checkBuffer json path args = case bufferArgs args of
  Nothing -> checkUsage
  Just buffers -> do
    input <- CE.try $ do
      src <- getContents >>= strict
      dependencies <- mapM (\(original, snapshot) -> do
        contents <- readFile snapshot >>= strict
        pure (original, contents)) buffers
      pure (src, dependencies)
    diagnostics <- case input of
      Left ex -> pure [Diagnostic (SourceSpan path 1 1 1 2) Error "load-error" (show (ex :: CE.IOException))]
      Right (src, dependencies) -> checkSource path src dependencies
    reportDiagnostics json [path] diagnostics
  where
    strict s = length s `seq` pure s
    bufferArgs [] = Just []
    bufferArgs ("--buffer" : original : snapshot : rest) = ((original, snapshot) :) <$> bufferArgs rest
    bufferArgs _ = Nothing

checkUsage :: IO ()
checkUsage = hPutStrLn stderr
  "Usage: infera check [--json] FILE... | infera check [--json] --stdin FILE [--buffer SOURCE SNAPSHOT]..." >> exitFailure

reportDiagnostics :: Bool -> [FilePath] -> [Diagnostic] -> IO ()
reportDiagnostics json paths diagnostics = do
  if json
    then putStrLn (diagnosticsJSON diagnostics)
    else do
      mapM_ (hPutStrLn stderr . renderDiagnostic) diagnostics
      if any ((== Error) . diagnosticSeverity) diagnostics
        then pure ()
        else mapM_ (\path -> putStrLn (path ++ ": ok")) paths
  if any ((== Error) . diagnosticSeverity) diagnostics then exitFailure else pure ()
