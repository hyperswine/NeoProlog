-- Run one checked tail loop per process, for example with +RTS -T -s.
-- Process-local RTS maxima must be compared across fresh processes, not
-- successive sizes in the same process. Parsing happens before timing.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.List (intercalate, isPrefixOf)
import Data.Version (showVersion)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Fingerprint (fingerprintString)
import GHC.Stats
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax (Query (..), parseQuery)
import System.Environment (getArgs)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Mem (performGC)
import Text.Read (readMaybe)

data Case = Ground | Result | Structured | Mutual | Helper | Choice | Once
  | Call | Conditional | Collected | Constrained | Cached | Dynamic
  deriving (Eq)

data Options = Options Int Bool Case

-- Keep the historical scalar fixture as the default. The additional cases
-- distinguish a free result from a fixed structured input with a shared leaf.
fixture :: Case -> Int -> (String, String, String, [String])
fixture Ground count = ("ground-integer-self-tail", groundSource,
  "down " ++ show count ++ "?", ["true."])
fixture Result count = ("free-result-self-tail", resultSource,
  "down_result " ++ show count ++ " R?", ["R = done"])
fixture Structured count = ("structured-shared-leaf-self-tail", structuredSource,
  "down_structured " ++ show count ++ " (box Leaf) R?",
  ["Leaf = done, R = box done"])
fixture Mutual count = ("mutual-free-result-tail", mutualSource,
  "even " ++ show count ++ " R?", ["R = done"])
fixture Helper count = ("prefix-helper-self-tail", helperSource,
  "down_helper " ++ show count ++ " R?", ["R = done"])
fixture Choice count = ("tail-with-caller-choice", resultSource,
  "(down_result " ++ show count ++ " R ; R = fallback)?", ["R = done", "R = fallback"])
fixture Once count = ("tail-in-once-scope", resultSource,
  "once (down_result " ++ show count ++ " R)?", ["R = done"])
fixture Call count = ("tail-in-call-scope", resultSource,
  "call (down_result " ++ show count ++ " R)?", ["R = done"])
fixture Conditional count = ("tail-in-if-condition", resultSource,
  "(down_result " ++ show count ++ " R -> R = done ; R = fallback)?", ["R = done"])
fixture Collected count = ("tail-in-findall-scope", resultSource,
  "findall R (down_result " ++ show count ++ " R) List?", ["List = [done]"])
fixture Constrained count = ("tail-with-live-clp-state", resultSource,
  "X in 1..3, Y #= X + 1, down_result " ++ show count ++ " R, label [X, Y]?",
  ["X = 1, Y = 2, R = done", "X = 2, Y = 3, R = done", "X = 3, Y = 4, R = done"])
fixture Cached count = ("tail-with-completed-table", resultSource ++ unlines
    ["cached : table.", "cached X <- cached X.", "cached seed."],
  "cached Before, down_result " ++ show count ++ " R, cached After?",
  ["Before = seed, R = done, After = seed"])
fixture Dynamic count = ("tail-with-dynamic-state", resultSource ++ "fact : dynamic.\n",
  "assert (fact seed), down_result " ++ show count ++ " R, fact Saved?",
  ["R = done, Saved = seed"])

groundSource :: String
groundSource = unlines
  [ "<- notable.",
    "down 0.",
    "down N <- N > 0, M is N - 1, down M."
  ]

resultSource :: String
resultSource = unlines
  [ "<- notable.",
    "down_result 0 R <- R = done.",
    "down_result N R <- N > 0, M is N - 1, down_result M R."
  ]

structuredSource :: String
structuredSource = unlines
  [ "<- notable.",
    "down_structured 0 (box Leaf) R <- Leaf = done, R = (box Leaf).",
    "down_structured N Data R <- N > 0, M is N - 1, down_structured M Data R."
  ]

mutualSource :: String
mutualSource = unlines
  [ "<- notable.",
    "even 0 done.",
    "even N R <- N > 0, M is N - 1, odd M R.",
    "odd 0 done.",
    "odd N R <- N > 0, M is N - 1, even M R."
  ]

helperSource :: String
helperSource = unlines
  [ "<- notable.",
    "step N M <- M is N - 1.",
    "down_helper 0 done.",
    "down_helper N R <- N > 0, step N M, down_helper M R."
  ]

usage :: String
usage = "Usage: machine-tail [iterations] [--case ground|result|structured|mutual|helper|choice|once|call|if|findall|clp|cached|dynamic] [--unmeasured] +RTS -T -s"

-- Flags and the single positional count can occur in any order. Rejecting
-- duplicate or unknown inputs avoids silently measuring a different fixture.
parseOptions :: [String] -> Either String Options
parseOptions = parse Nothing Nothing Nothing
  where
    parse count measured chosen [] = Right $ Options
      (maybe 1000000 id count) (maybe True id measured) (maybe Ground id chosen)
    parse count Nothing chosen ("--unmeasured" : rest) = parse count (Just False) chosen rest
    parse _ (Just _) _ ("--unmeasured" : _) = Left "Duplicate --unmeasured flag"
    parse count measured Nothing ("--case" : name : rest) = do
      selected <- case name of
        "ground" -> Right Ground
        "result" -> Right Result
        "structured" -> Right Structured
        "mutual" -> Right Mutual
        "helper" -> Right Helper
        "choice" -> Right Choice
        "once" -> Right Once
        "call" -> Right Call
        "if" -> Right Conditional
        "findall" -> Right Collected
        "clp" -> Right Constrained
        "cached" -> Right Cached
        "dynamic" -> Right Dynamic
        _ -> Left ("Unknown tail case: " ++ name)
      parse count measured (Just selected) rest
    parse _ _ (Just _) ("--case" : _) = Left "Duplicate --case flag"
    parse _ _ _ ["--case"] = Left "Missing value after --case"
    parse count measured chosen (text : rest)
      | "--" `isPrefixOf` text = Left ("Unknown option: " ++ text)
      | otherwise = case count of
          Just _ -> Left "Only one iteration count may be supplied"
          Nothing -> case readMaybe text of
            Just value | value >= (0 :: Int) -> parse (Just value) measured chosen rest
            _ -> Left "Iteration count must be a nonnegative machine integer"

-- Fully drain the continuation. Keep only projected observations rather than
-- retaining all intermediate checkpoints or the lazy answer stream's head.
drain :: Query -> Machine.Checkpoint -> Either Heap.HeapError ([String], Machine.Metrics)
drain query checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], Machine.checkpointMetrics checkpoint)
    Machine.Yield item next -> case item of
      Reference.Found state -> do
        let answer = Reference.projectAnswer query state
        unless (null (Reference.answerOutput answer)) (Left Heap.IncompatibleBindings)
        (rest, metrics) <- drain query next
        pure (Reference.showAnswer answer : rest, metrics)
      _ -> Left Heap.IncompatibleBindings

json :: [(String, String)] -> String
json fields = "{" ++ intercalate "," [show key ++ ":" ++ value | (key, value) <- fields] ++ "}"

metricFields :: Machine.Metrics -> [(String, String)]
metricFields metrics =
  [ ("calls", show (Machine.metricCalls metrics)),
    ("tail_calls", show (Machine.metricTailCalls metrics)),
    ("collections", show (Machine.metricCollections metrics)),
    ("max_tasks", show (Machine.metricMaxTasks metrics)),
    ("max_choices", show (Machine.metricMaxChoices metrics)),
    ("max_scopes", show (Machine.metricMaxScopes metrics)),
    ("max_cut_owners", show (Machine.metricMaxCutOwners metrics)),
    ("max_heap_cells", show (Machine.metricMaxHeapCells metrics)),
    ("max_trail_entries", show (Machine.metricMaxTrailEntries metrics)),
    ("max_bindings", show (Machine.metricMaxBindings metrics)),
    ("max_substitutions", show (Machine.metricMaxSubstitutions metrics)),
    ("max_constants", show (Machine.metricMaxConstants metrics)),
    ("max_functors", show (Machine.metricMaxFunctors metrics))
  ]

main :: IO ()
main = do
  arguments <- getArgs
  Options count measured selected <- either (fail . (++ "\n" ++ usage)) pure (parseOptions arguments)
  let (caseName, source, querySource, expected) = fixture selected count
  enabled <- getRTSStatsEnabled
  unless enabled (fail "Enable RTS statistics with +RTS -T -s")
  program <- either fail pure (Reference.loadProgramText source)
  query <- either fail pure (parseQuery querySource)
  _ <- evaluate (length (show program) + length (show query))
  let paths = ["src/Infera/Machine/Control.hs", "src/Infera/Machine/Heap.hs",
        "src/Infera/Machine/Bridge.hs", "src/Infera/Machine/CLP.hs",
        "src/Infera/Machine/Builtins.hs", "src/Infera/Machine/Tail.hs",
        "src/Infera/Machine/Table.hs", "src/Infera/Engine/Reference.hs",
        "src/Infera/Engine.hs", "src/Infera/Engine/Contracts.hs", "src/Infera/Arith.hs",
        "src/Infera/CLP.hs", "src/Infera/Unify.hs", "src/Infera/Program.hs",
        "src/Infera/Syntax.hs", "src/Infera/Machine/Trace/Types.hs", "bench/machine-tail.hs"]
  contents <- mapM (\path -> readFile path >>= \text -> pure (path ++ "\n" ++ text)) paths
  let fingerprint = show (fingerprintString
        (caseName ++ source ++ querySource ++ show expected ++ concat contents))
  _ <- evaluate (length fingerprint)
  performGC
  before <- getRTSStats
  started <- getMonotonicTimeNSec
  let begin = if measured then Machine.startMeasured else Machine.start
      result = begin program query >>= drain query
  (answers, metrics) <- either (fail . show) pure result
  _ <- evaluate (length (show answers) + length (show (metricFields metrics)))
  unless (answers == expected) (fail ("Tail loop did not produce its verified answer: " ++ show answers))
  unless (not measured || Machine.metricCalls metrics >= count + 1)
    (fail "Call counter missed a loop activation")
  if measured && count >= 10000
    then do
      unless (Machine.metricTailCalls metrics > count - 1000) (fail "Tail loop did not reuse its frame")
      unless (Machine.metricCollections metrics > 0) (fail "Tail loop did not exercise collection")
    else pure ()
  ended <- getMonotonicTimeNSec
  performGC
  after <- getRTSStats
  putStrLn $ json
    [ ("case", show caseName),
      ("iterations", show count),
      ("verified_answers", show (length expected)),
      ("fully_drained", "true"),
      ("measured", if measured then "true" else "false"),
      ("metric_counter_policy", show (if measured then "enabled" else "disabled; all counters are zero" :: String)),
      ("source_fingerprint", show fingerprint),
      ("compiler", show (compilerName ++ "-" ++ showVersion compilerVersion)),
      ("platform", show (arch ++ "-" ++ os)),
      ("scope", show ("loaded program execution, projection and validation; one fresh process" :: String)),
      ("wall_seconds", show (fromIntegral (ended - started) / 1.0e9 :: Double)),
      ("execution_allocated_bytes", show (allocated_bytes after - allocated_bytes before)),
      ("process_max_live_bytes", show (max_live_bytes after)),
      ("final_live_bytes", show (gcdetails_live_bytes (gc after))),
      ("execution_gcs", show (gcs after - gcs before)),
      ("execution_major_gcs", show (major_gcs after - major_gcs before)),
      ("metrics", json (metricFields metrics))
    ]
