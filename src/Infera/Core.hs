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
    solveQueryWith,
    solveQueryOrFallback,
    coreSupports,
    coreOutcome,
  )
where

import Infera.Core.Run (Step (..), runCore, runCoreWith)
import Infera.Engine.Reference (Search)
import qualified Infera.Machine.Control as Machine
import Infera.Program (Program)
import Infera.Syntax (Query)
import System.IO.Unsafe (unsafeInterleaveIO, unsafePerformIO)

-- | Solve on the core. A construct the core cannot execute abandons the
-- run and the remaining items come from the existing machine, skipping the
-- prefix already produced; solving is a pure function of program and
-- query, so the two prefixes agree. (Nothing is reserved for a future
-- program-level rejection; every program currently starts on the core.)
solveQuery :: Program -> Query -> Maybe Search
solveQuery program query = unsafePerformIO $ do
  (_, first) <- runCore program query
  Just <$> stream (0 :: Int) first
  where
    stream produced next = unsafeInterleaveIO $ do
      step <- next
      case step of
        Stop -> pure []
        Yield item continue -> (item :) <$> stream (produced + 1) continue
        Abandon _ -> pure (drop produced (Machine.solveQuery program query))
{-# NOINLINE solveQuery #-}

-- | 'solveQuery' with an explicit initial collection threshold in cells.
solveQueryWith :: Int -> Program -> Query -> Maybe Search
solveQueryWith limit program query = unsafePerformIO $ do
  (_, first) <- runCoreWith limit program query
  Just <$> stream (0 :: Int) first
  where
    stream produced next = unsafeInterleaveIO $ do
      step <- next
      case step of
        Stop -> pure []
        Yield item continue -> (item :) <$> stream (produced + 1) continue
        Abandon _ -> pure (drop produced (Machine.solveQuery program query))
{-# NOINLINE solveQueryWith #-}

-- | The core when it applies, otherwise the existing machine.
solveQueryOrFallback :: Program -> Query -> Search
solveQueryOrFallback program query =
  maybe (Machine.solveQuery program query) id (solveQuery program query)

-- | Nothing when every construct of this program and query runs on the
-- core, otherwise the first one that would make a run fall back.
coreSupports :: Program -> Query -> Maybe String
coreSupports program query = unsafePerformIO (fst <$> runCore program query)
{-# NOINLINE coreSupports #-}

-- | Run a query to completion on the core alone: the item count, or the
-- reason the run was abandoned.
coreOutcome :: Program -> Query -> IO (Either String Int)
coreOutcome program query = do
  (_, first) <- runCore program query
  let go count next = do
        step <- next
        case step of
          Stop -> pure (Right count)
          Yield _ continue -> go (count + 1 :: Int) continue
          Abandon reason -> pure (Left reason)
  go 0 first
