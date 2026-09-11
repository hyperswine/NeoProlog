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
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("reg" : paths) -> mapM_ registerModule paths
    _ -> runRepl
