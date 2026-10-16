-- | Immutable source identities and execution events. These values contain no
-- heap handles and may be retained independently of a suspended query.
module Infera.Machine.Trace.Types
  ( SourceMap,
    ClauseSource (..),
    emptySourceMap,
    sourceMap,
    appendSourceMap,
    lookupClauseSource,
    goalSourceSpan,
    TracePort (..),
    TraceFrame (..),
    TraceEvent (..),
    renderTraceEvent,
    renderSourceSpan,
  )
where

import Data.List (foldl', intercalate)
import qualified Data.Map.Strict as Map
import Infera.Error (PredKey, SolveError, showPredKey, showSolveError)
import Infera.Syntax

-- | Clause ordinals follow 'Infera.Program.addClause', independently for
-- each predicate. Retaining the ordinal distinguishes identical clauses.
newtype SourceMap = SourceMap (Map.Map (PredKey, Int) ClauseSource)
  deriving (Eq, Show)

data ClauseSource = ClauseSource
  { sourceClauseSpan :: SourceSpan,
    sourceHeadSpan :: SourceSpan,
    sourceGoalSpans :: [(Term, SourceSpan)]
  }
  deriving (Eq, Show)

emptySourceMap :: SourceMap
emptySourceMap = SourceMap Map.empty

-- | Build metadata from the same expanded, qualified items used to build the
-- predicate table. Imported file identities and UTF-16 ranges stay intact.
sourceMap :: [LocatedTopLevel] -> SourceMap
sourceMap = appendSourceMap emptySourceMap

-- | Extend metadata when clauses are entered interactively. Existing loaded
-- ordinals retain their identities; new clauses start after them.
appendSourceMap :: SourceMap -> [LocatedTopLevel] -> SourceMap
appendSourceMap (SourceMap existing) items = SourceMap (snd (foldl' add (initialCounts, existing) items))
  where
    initialCounts = Map.fromListWith max [(key, ordinal + 1) | ((key, ordinal), _) <- Map.toList existing]
    add (counts, sources) item = case locatedItem item of
      TLClause clause | Just key <- clauseKey clause ->
        let ordinal = Map.findWithDefault 0 key counts
            span' = locatedSpan item
            source = ClauseSource span'
              (maybe span' id (locatedHeadSpan item)) (locatedGoalSpans item)
         in (Map.insert key (ordinal + 1) counts,
             Map.insert (key, ordinal) source sources)
      _ -> (counts, sources)

lookupClauseSource :: SourceMap -> PredKey -> Int -> Maybe ClauseSource
lookupClauseSource (SourceMap sources) key ordinal = Map.lookup (key, ordinal) sources

-- | Generated DCG/control code and ambiguous equal occurrences use their
-- owning clause span. Never guess which textual occurrence was executed.
goalSourceSpan :: ClauseSource -> Term -> SourceSpan
goalSourceSpan source goal = case [span' | (term, span') <- sourceGoalSpans source, term == goal] of
  [span'] -> span'
  _ -> sourceClauseSpan source

data TracePort = Call | Exit | Redo | Fail | Cut | Exception
  deriving (Eq, Show)

-- | The nearest activation is first. Clause ordinals are zero based, as in
-- the loaded predicate table; rendering displays them as one based.
data TraceFrame = TraceFrame
  { traceFramePredicate :: PredKey,
    traceFrameClause :: Maybe Int,
    traceFrameSpan :: Maybe SourceSpan
  }
  deriving (Eq, Show)

data TraceEvent = TraceEvent
  { tracePort :: TracePort,
    traceGoal :: Term,
    traceSpan :: Maybe SourceSpan,
    traceFrames :: [TraceFrame],
    traceError :: Maybe SolveError
  }
  deriving (Eq, Show)

renderSourceSpan :: SourceSpan -> String
renderSourceSpan span' = spanFile span' ++ ":" ++ show (spanLine span') ++ ":" ++ show (spanColumn span')

renderTraceEvent :: TraceEvent -> String
renderTraceEvent event = show (tracePort event) ++ " " ++ show (traceGoal event)
  ++ maybe "" ((" at " ++) . renderSourceSpan) (traceSpan event)
  ++ maybe "" ((": " ++) . showSolveError) (traceError event)
  ++ case traceFrames event of
    [] -> ""
    frames -> " [" ++ intercalate " <- " (map renderFrame frames) ++ "]"
  where
    renderFrame frame = showPredKey (traceFramePredicate frame)
      ++ maybe "" ((" clause " ++) . show . (+ 1)) (traceFrameClause frame)
