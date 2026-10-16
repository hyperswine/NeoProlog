-- One checked cold or warm query per fresh process. Loading/checking and the
-- Reference oracle stay outside timing. Cold has no native/compiled preprobe;
-- warm drains a distinct query first, sharing only immutable program caches.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, unless, when)
import Data.List (intercalate, sort)
import Data.Version (showVersion)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Fingerprint (fingerprintString)
import Infera hiding (main)
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import System.CPUTime (getCPUTime)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs)
import System.FilePath ((</>), takeExtension)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Timeout (timeout)
import Text.Read (readMaybe)

data Engine = Reference | Interpreted | Bytecode deriving (Eq)
data Phase = Cold | Warm deriving (Eq)
data Workload = Helper Int | StructuredHeads | Controls | Minefield deriving (Eq)
data Options = Options Engine Phase Workload Double
data Model = ExactInteger Integer | BinaryGrid Int Integer

usage :: String
usage = "Usage: machine-cache --engine reference|interpreted|bytecode --phase cold|warm --case helper-0|helper-100|helper-1000|structured-head|controls|minefield-16 [--timeout seconds]"

parseOptions :: [String] -> Either String Options
parseOptions = parse Nothing Nothing Nothing Nothing
  where
    parse engine phase workload budget [] = Options
      <$> required "--engine" engine <*> required "--phase" phase
      <*> required "--case" workload <*> pure (maybe 30 id budget)
    parse Nothing phase workload budget ("--engine" : value : rest) = do
      chosen <- case value of
        "reference" -> Right Reference
        "interpreted" -> Right Interpreted
        "bytecode" -> Right Bytecode
        _ -> Left ("Unknown engine: " ++ value)
      parse (Just chosen) phase workload budget rest
    parse engine Nothing workload budget ("--phase" : value : rest) = do
      chosen <- case value of
        "cold" -> Right Cold
        "warm" -> Right Warm
        _ -> Left ("Unknown phase: " ++ value)
      parse engine (Just chosen) workload budget rest
    parse engine phase Nothing budget ("--case" : value : rest) = do
      chosen <- case value of
        "helper-0" -> Right (Helper 0)
        "helper-100" -> Right (Helper 100)
        "helper-1000" -> Right (Helper 1000)
        "structured-head" -> Right StructuredHeads
        "controls" -> Right Controls
        "minefield-16" -> Right Minefield
        _ -> Left ("Unknown case: " ++ value)
      parse engine phase (Just chosen) budget rest
    parse engine phase workload Nothing ("--timeout" : value : rest) = case readMaybe value of
      Just chosen | chosen > 0 && chosen <= 86400 && not (isInfinite chosen) && not (isNaN chosen) ->
        parse engine phase workload (Just chosen) rest
      _ -> Left "Timeout must be finite and between 0 and 86400 seconds"
    parse _ _ _ _ [flag] | flag `elem` ["--engine", "--phase", "--case", "--timeout"] =
      Left ("Missing value after " ++ flag)
    parse _ _ _ _ (flag : _) = Left ("Duplicate or unknown option: " ++ flag)
    required name = maybe (Left ("Missing " ++ name)) Right

workloadName :: Workload -> String
workloadName workload = case workload of
  Helper padding -> "helper-" ++ show padding
  StructuredHeads -> "structured-head"
  Controls -> "controls"
  Minefield -> "minefield-16"

fixture :: Workload -> IO (String, String, Model)
fixture workload = case workload of
  Helper padding -> pure (unlines
    ([ "<- notable.",
       "step N Acc M Next <- M is N - 1, Next is Acc + N.",
       "loop 0 Acc Acc.",
       "loop N Acc Result <- N > 0, step N Acc M Next, loop M Next Result."
     ] ++ ["unused_" ++ show index ++ " padding." | index <- [1 .. padding]]),
    "loop 10000 0 Result?", ExactInteger 50005000)
  StructuredHeads -> pure (unlines
    [ "<- notable.",
      "read_node (node (pair X X) [X, X, X] (tag X X X)) X.",
      "head_loop 0 Acc Acc.",
      "head_loop N Acc Result <- N > 0, read_node (node (pair N N) [N, N, N] (tag N N N)) Value, M is N - 1, Next is Acc + Value, head_loop M Next Result."
    ], "head_loop 10000 0 Result?", ExactInteger 50005000)
  Controls -> pure (unlines
    [ "<- notable.",
      "loop 0 Acc Acc.",
      "loop N Acc Result <- N > 0, once ((Picked = N ; Picked = 0)), not (Picked < 0), (Picked > 0 -> Next is Acc + Picked ; Next = Acc), M is N - 1, loop M Next Result."
    ], "loop 300 0 Result?", ExactInteger 45150)
  Minefield -> do
    source <- readFile "examples/minesweeper.nprolog"
    pure (source, "once (minefield 16 16 50 [window 2 2 2] Result)?", BinaryGrid 16 50)

data Observation
  = AnswerObservation [(String, Term)] [String] [OutputEvent]
  | ErrorObservation SolveError
  | ExhaustionObservation
  | CutObservation Int
  | IncompleteObservation Term
  deriving (Eq, Show)

observe :: Query -> Search -> [Observation]
observe query = map item
  where
    item (Found state) = let answer = projectAnswer query state in
      AnswerObservation (answerBindings answer) (answerResiduals answer) (answerOutput answer)
    item (BranchError problem) = ErrorObservation problem
    item BranchExhausted = ExhaustionObservation
    item (CutMarker owner) = CutObservation owner
    item (ConsumedIncomplete key) = IncompleteObservation key

-- Keep a fresh logical base in every search. Program/cache objects are shared
-- deliberately; heaps, persistent Stores, table answers and dynamic facts are
-- new query state, never an evaluated answer stream or checkpoint replay.
{-# NOINLINE execute #-}
execute :: Int -> Engine -> Program -> Query -> [Observation]
execute serial engine program query = observe query (resolver program shifted)
  where
    shifted = query {queryNVars = queryNVars query + serial}
    resolver = case engine of
      Reference -> Reference.solveQuery
      Interpreted -> Machine.solveQueryWithBackend Machine.Interpreted
      Bytecode -> Machine.solveQueryWithBackend Machine.Bytecode

forceObservations :: [Observation] -> IO ()
forceObservations observations = do
  _ <- evaluate (length (show observations))
  pure ()

independent :: Model -> [Observation] -> Either String ()
independent (ExactInteger value) actual = unless
  (actual == [AnswerObservation [("Result", IntLit value)] [] []])
  (Left "Independent integer/ordered-stream model failed")
independent (BinaryGrid size bombs) actual = do
  grid <- case actual of
    [AnswerObservation [("Result", value)] [] []] -> properList value >>= mapM properList
    _ -> Left "Expected exactly one ground grid without residuals/output/errors"
  unless (length grid == size && all ((== size) . length) grid) (Left "Incorrect grid dimensions")
  rows <- mapM (mapM binary) grid
  unless (sum (concat rows) == bombs) (Left "Incorrect bomb count")
  unless (and [sum [rows !! (y + dy) !! (x + dx) | dy <- [0, 1], dx <- [0, 1]] <= 2
    | y <- [0 .. size - 2], x <- [0 .. size - 2]]) (Left "Overlapping 2x2 window cap violated")
  where
    properList term = case unfoldCons term of
      (values, Nothing) -> Right values
      _ -> Left "Grid contains an improper list"
    binary (IntLit value) | value == 0 || value == 1 = Right value
    binary _ = Left "Grid contains a nonbinary or nonground cell"

validate :: Model -> [Observation] -> [Observation] -> IO ()
validate model expected actual = do
  either fail pure (independent model actual)
  unless (actual == expected) (fail "Complete ordered answer/residual/output/error stream differs from Reference")

within :: Int -> String -> IO value -> IO value
within budget stage action = timeout budget action >>= maybe
  (fail (stage ++ " exceeded its explicit timeout; no timing emitted")) pure

-- Force source and solver metadata without inspecting the lazy compiler cache
-- field. Even a future Show instance must not turn a cold row into a warm one.
forceUncachedProgram :: Program -> IO ()
forceUncachedProgram program = do
  let sourceMetadata definition = show
        (predKey definition, predClauses definition, predIndex definition,
          predDecls definition, predFlags definition, predInferred definition,
          predRecursive definition, predPure definition, predStructural definition)
      metadata = show (progOrder program, progNameFlags program, progFiles program,
        progTableDefault program, progIndexDefault program, progSources program)
  _ <- evaluate (sum (map (length . sourceMetadata) (programPreds program)) + length metadata)
  pure ()

runtimeSources :: FilePath -> IO [FilePath]
runtimeSources directory = do
  names <- listDirectory directory
  paths <- forM names $ \name -> do
    let path = directory </> name
    nested <- doesDirectoryExist path
    if nested then runtimeSources path else pure [path | takeExtension path == ".hs"]
  pure (sort (concat paths))

drain :: Machine.Checkpoint -> Either Heap.HeapError (Search, Machine.Metrics)
drain checkpoint = do
  next <- Machine.resume checkpoint
  case next of
    Machine.Finished -> pure ([], Machine.checkpointMetrics checkpoint)
    Machine.Yield item remaining -> do
      (rest, metrics) <- drain remaining
      pure (item : rest, metrics)

probe :: Int -> Workload -> Program -> Query -> Model -> [Observation] -> IO (Maybe Machine.Metrics)
probe budget workload program query model expected = Just <$> within budget "Post-timing bytecode probe" (do
  initial <- either (fail . show) pure (Machine.startMeasuredWithBackend Machine.Bytecode program
    (query {queryNVars = queryNVars query + 3}))
  (search, metrics) <- either (fail . show) pure (drain initial)
  let actual = observe query search
  forceObservations actual
  validate model expected actual
  unless (Machine.metricCompiledActivations metrics > 0
    && Machine.metricCodeCacheHits metrics > 0
    && Machine.metricPredicateCacheHits metrics > 0
    && Machine.metricPredicateCacheMisses metrics == 0)
    (fail "Post-timing probe did not exercise compiled/cache paths")
  when (workload == Controls) $ unless (Machine.metricCompiledControlInstructions metrics > 0)
    (fail "Post-timing probe did not exercise compiled controls")
  pure metrics)

json :: [(String, String)] -> String
json fields = "{" ++ intercalate "," [show key ++ ":" ++ value | (key, value) <- fields] ++ "}"

metricFields :: Machine.Metrics -> [(String, String)]
metricFields metrics =
  [("compiled_activations", show (Machine.metricCompiledActivations metrics)),
   ("direct_calls", show (Machine.metricDirectCalls metrics)),
   ("compiled_control_instructions", show (Machine.metricCompiledControlInstructions metrics)),
   ("code_cache_hits", show (Machine.metricCodeCacheHits metrics)),
   ("predicate_cache_hits", show (Machine.metricPredicateCacheHits metrics)),
   ("predicate_cache_misses", show (Machine.metricPredicateCacheMisses metrics)),
   ("max_heap_cells", show (Machine.metricMaxHeapCells metrics)),
   ("max_activation_registers", show (Machine.metricMaxActivationRegisters metrics))]

main :: IO ()
main = do
  arguments <- getArgs
  Options engine phase workload seconds <- either (fail . (++ "\n" ++ usage)) pure (parseOptions arguments)
  let budget = round (seconds * 1000000)
      engineName = case engine of Reference -> "reference"; Interpreted -> "interpreted"; Bytecode -> "bytecode"
      phaseName = if phase == Cold then "cold" else "warm"
  (source, querySource, model) <- fixture workload
  items <- either fail pure (parseFile source)
  program <- either fail pure (buildChecked [item | item <- items, case item of TLQuery _ -> False; _ -> True])
  query <- either fail pure (parseQuery querySource)
  forceUncachedProgram program
  _ <- evaluate (length (show query) + length source)
  paths <- runtimeSources "src"
  sources <- mapM (\path -> readFile path >>= \contents -> pure (path ++ "\n" ++ contents))
    (paths ++ ["bench/machine-cache.hs"])
  let fingerprint = show (fingerprintString (concat sources))
      workloadFingerprint = show (fingerprintString (source ++ querySource))
  _ <- evaluate (length fingerprint + length workloadFingerprint)
  let expected = execute 0 Reference program query
  within budget "Reference oracle" $ do
    forceObservations expected
    either fail pure (independent model expected)
  when (phase == Warm) $ within budget "Checked warmup" $ do
    let warmed = execute 1 engine program query
    forceObservations warmed
    validate model expected warmed
  started <- getMonotonicTimeNSec
  cpuStarted <- getCPUTime
  actual <- within budget "Timed query" $ do
    let result = execute 2 engine program query
    forceObservations result
    validate model expected result
    pure result
  cpuEnded <- getCPUTime
  ended <- getMonotonicTimeNSec
  -- Cold's first compiled/native invocation has already completed. Only now
  -- may the measured probe force compiler/cache state for path verification.
  metrics <- if engine == Bytecode then probe budget workload program query model expected else pure Nothing
  putStrLn (json
    [("engine", show engineName), ("phase", show phaseName), ("case", show (workloadName workload)),
     ("padding_predicates", show (case workload of Helper padding -> padding; _ -> 0)),
     ("status", show ("ok" :: String)), ("timeout_seconds", show seconds),
     ("source_fingerprint", show fingerprint), ("workload_fingerprint", show workloadFingerprint),
     ("compiler", show (compilerName ++ "-" ++ showVersion compilerVersion)),
     ("platform", show (arch ++ "-" ++ os)),
     ("scope", show ("loaded checked program; first native/compiled query for cold or query after one checked warmup; execution+projection+validation; one sample per fresh process" :: String)),
     ("build", show ("runner -O2; library optimization follows Cabal configuration" :: String)),
     ("warmup_queries", if phase == Cold then "0" else "1"),
     ("fresh_query_state", "true"), ("fully_drained", "true"),
     ("oracle_checked", "true"), ("independent_checked", "true"),
     ("verified_answers", show (length [() | AnswerObservation _ _ _ <- actual])),
     ("answer_fingerprint", show (show (fingerprintString (show actual)))),
     ("wall_seconds", show (fromIntegral (ended - started) / 1.0e9 :: Double)),
     ("cpu_seconds", show (fromIntegral (cpuEnded - cpuStarted) / 1.0e12 :: Double)),
     ("timed_instruction_counters", "false"), ("probe_timed", "false"),
     ("post_timing_probe", maybe "null" (json . metricFields) metrics)])
