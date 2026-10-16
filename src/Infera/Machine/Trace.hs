-- | Lazy, opt-in tracing over the native driver's immutable checkpoints.
-- Normal solving neither records nor retains trace events.
module Infera.Machine.Trace
  ( TraceItem (..),
    traceQuery,
    traceSearch,
    module Infera.Machine.Trace.Types,
  )
where

import Infera.Engine (Search, SearchItem (..))
import Infera.Error (SolveError (UserError))
import qualified Infera.Machine.Control as Control
import qualified Infera.Machine.Heap as Heap
import Infera.Machine.Trace.Types
import Infera.Program (Program)
import Infera.Syntax (Query)

data TraceItem = TraceEventItem TraceEvent | TraceSearchItem SearchItem

-- | Events precede their corresponding public result. Discarding events
-- reproduces the ordinary query stream, including branch issues and markers.
traceQuery :: Program -> Query -> [TraceItem]
traceQuery program query = unfold (Control.startTraced program query)
  where
    unfold :: Either Heap.HeapError Control.Checkpoint -> [TraceItem]
    unfold (Left err) = [TraceSearchItem (BranchError (UserError ("machine heap: " ++ show err)))]
    unfold (Right checkpoint) = case Control.resumeTraced checkpoint of
      Left err -> unfold (Left err)
      Right (events, step) -> map TraceEventItem events ++ case step of
        Control.Finished -> []
        Control.Yield item next -> TraceSearchItem item : unfold (Right next)

traceSearch :: [TraceItem] -> Search
traceSearch [] = []
traceSearch (TraceEventItem _ : rest) = traceSearch rest
traceSearch (TraceSearchItem item : rest) = item : traceSearch rest
