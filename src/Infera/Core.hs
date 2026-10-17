-- | The core resolution engine behind the public lazy 'Search' boundary.
--
-- 'solveQuery' returns the same immutable item stream as the reference and
-- the existing machine. Internally one mutable machine runs in 'IO' and the
-- list is produced by interleaved resumption: each element forces the
-- previous one, so the sequence is a function of the program and query
-- alone, consuming a prefix is safe, and a retained 'Found' state stays
-- valid because it was exported when it was produced.
module Infera.Core
  ( solveQuery,
    solveQueryOrFallback,
    coreSupports,
  )
where

import Infera.Core.Run (Step (..), runCore)
import Infera.Engine.Reference (Search)
import qualified Infera.Machine.Control as Machine
import Infera.Program (Program)
import Infera.Syntax (Query)
import System.IO.Unsafe (unsafeInterleaveIO, unsafePerformIO)

-- | Solve on the core, or Nothing when the program is outside its subset.
-- A construct met at runtime that the core cannot execute abandons the run
-- and the remaining items come from the existing machine, skipping the
-- prefix already produced; solving is a pure function of program and
-- query, so the two prefixes agree.
solveQuery :: Program -> Query -> Maybe Search
solveQuery program query = unsafePerformIO $ do
  started <- runCore program query
  case started of
    Left _ -> pure Nothing
    Right first -> Just <$> stream (0 :: Int) first
  where
    stream produced next = unsafeInterleaveIO $ do
      step <- next
      case step of
        Stop -> pure []
        Yield item continue -> (item :) <$> stream (produced + 1) continue
        Abandon _ -> pure (drop produced (Machine.solveQuery program query))
{-# NOINLINE solveQuery #-}

-- | The core when it applies, otherwise the existing machine.
solveQueryOrFallback :: Program -> Query -> Search
solveQueryOrFallback program query =
  maybe (Machine.solveQuery program query) id (solveQuery program query)

-- | Nothing when the core compiles this program and query, otherwise the
-- construct that keeps it on the existing machine.
coreSupports :: Program -> Query -> Maybe String
coreSupports program query = unsafePerformIO $ do
  started <- runCore program query
  pure (either Just (const Nothing) started)
{-# NOINLINE coreSupports #-}
