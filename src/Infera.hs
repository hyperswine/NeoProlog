-- | Infera v2: a Prolog-inspired logic language with sorts, modes,
-- determinism, indexing, tabling and CLP(Z).
--
-- This module re-exports the public surface and provides 'main'.
module Infera
  ( module Infera.Syntax,
    module Infera.Error,
    module Infera.Unify,
    module Infera.Arith,
    module Infera.CLP,
    module Infera.Program,
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
import Infera.Infer
import Infera.Module
import Infera.Program
import Infera.Repl
import Infera.Syntax
import Infera.Unify
import qualified Data.IntMap.Strict as IM
import Control.Monad (forM)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("reg" : paths) -> mapM_ registerModule paths
    ("check" : paths) -> checkFiles paths
    _ -> runRepl

-- | @infera check FILE...@: load each file (resolving imports and running the
-- analyses) and report parse or module errors.  Exits non-zero on failure.
checkFiles :: [FilePath] -> IO ()
checkFiles paths = do
  results <- forM paths $ \path -> do
    res <- loadFile path
    case res of
      Left err -> do
        hPutStrLn stderr (path ++ ": error: " ++ err)
        return False
      Right (prog, queries) -> do
        let n = sum [IM.size (predClauses p) | p <- programPreds prog]
        putStrLn (path ++ ": ok (" ++ show n ++ " clauses, " ++ show (length queries) ++ " queries)")
        return True
  if and results then return () else exitFailure
