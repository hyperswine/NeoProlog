-- One loaded-program sample per fresh process. Run native and reference in
-- separate invocations; native samples check an untimed reference oracle.
-- Setup deliberately leaves cells unlabelled, so its validation compares the
-- complete projected constraints rather than claiming to validate a grid.
module Main (main) where

import Control.Exception (IOException, evaluate, try)
import Control.Monad (unless)
import Data.List (intercalate)
import Data.Version (showVersion)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Fingerprint (fingerprintString)
import Infera hiding (main)
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Timeout (timeout)
import Text.Read (readMaybe)

data Engine = Native | Bytecode | Reference deriving (Eq)
data Phase = Setup | Ordinary deriving (Eq)
data Options = Options Engine Phase Int Integer Double Bool

usage :: String
usage = "Usage: machine-minefield [--engine native|bytecode|reference] [--phase setup|ordinary] [--size N] [--bombs N] [--timeout SECONDS] [--measured]"

parseOptions :: [String] -> Either String Options
parseOptions = go Nothing Nothing Nothing Nothing Nothing False
  where
    go engine phase size bombs budget measured [] = do
      let width = maybe 16 id size
          count = maybe (min 50 (toInteger width * toInteger width `div` 2)) id bombs
          chosen = maybe Native id engine
      unless (count <= toInteger width * toInteger width) (Left "Bomb count exceeds board capacity")
      unless (not measured || chosen /= Reference) (Left "--measured requires a native engine")
      pure (Options chosen (maybe Ordinary id phase) width count (maybe 30 id budget) measured)
    go Nothing phase size bombs budget measured ("--engine" : value : rest) = do
      engine <- case value of
        "native" -> Right Native
        "bytecode" -> Right Bytecode
        "reference" -> Right Reference
        _ -> Left "Engine must be native, bytecode or reference"
      go (Just engine) phase size bombs budget measured rest
    go engine Nothing size bombs budget measured ("--phase" : value : rest) = do
      phase <- case value of
        "setup" -> Right Setup
        "ordinary" -> Right Ordinary
        _ -> Left "Phase must be setup or ordinary"
      go engine (Just phase) size bombs budget measured rest
    go engine phase Nothing bombs budget measured ("--size" : value : rest) = do
      size <- number "Size must be a positive machine integer" (> (0 :: Int)) value
      go engine phase (Just size) bombs budget measured rest
    go engine phase size Nothing budget measured ("--bombs" : value : rest) = do
      bombs <- number "Bomb count must be a nonnegative integer" (>= (0 :: Integer)) value
      go engine phase size (Just bombs) budget measured rest
    go engine phase size bombs Nothing measured ("--timeout" : value : rest) = do
      budget <- number "Timeout must be a positive finite number of seconds" validBudget value
      go engine phase size bombs (Just budget) measured rest
    go engine phase size bombs budget False ("--measured" : rest) =
      go engine phase size bombs budget True rest
    go _ _ _ _ _ _ (flag : _) = Left ("Unknown, duplicate or incomplete option: " ++ flag)
    number message valid value = case readMaybe value of
      Just parsed | valid parsed -> Right parsed
      _ -> Left message
    validBudget value = value > 0 && not (isInfinite value) && not (isNaN value)
      && value <= fromIntegral (maxBound :: Int) / 1000000

asList :: Term -> Either String [Term]
asList term = case unfoldCons term of
  (values, Nothing) -> Right values
  _ -> Left ("Expected a proper list: " ++ show term)

binding :: String -> Answer -> Either String Term
binding name answer = maybe (Left ("Missing binding " ++ name)) Right (lookup name (answerBindings answer))

validate :: Phase -> Int -> Integer -> QuerySummary -> Either String ()
validate phase size bombs summary = do
  unless (null (summaryErrors summary)) (Left (show (summaryErrors summary)))
  unless (not (summaryExhausted summary)) (Left "Resolution exhausted")
  answer <- case summaryAnswers summary of
    [one] -> Right one
    _ -> Left "Expected exactly one answer"
  unless (null (answerOutput answer)) (Left "Unexpected output")
  grid <- binding "Grid" answer >>= asList >>= mapM asList
  unless (length grid == size && all ((== size) . length) grid) (Left "Incorrect grid dimensions")
  case phase of
    Setup -> do
      cells <- binding "Cells" answer >>= asList
      unless (cells == concat grid) (Left "Flattened cells differ from grid")
      unless (all validCell cells) (Left "Invalid setup cell")
      unless (all groundBinary cells || not (null (answerResiduals answer))) (Left "Missing setup constraints")
    Ordinary -> do
      rows <- mapM (mapM groundCell) grid
      unless (sum (concat rows) == bombs) (Left "Incorrect bomb count")
      unless (and [sum [rows !! (y + dy) !! (x + dx) | dy <- [0, 1], dx <- [0, 1]] <= 2
                   | y <- [0 .. size - 2], x <- [0 .. size - 2]]) (Left "Overlapping 2x2 window cap violated")
      unless (null (answerResiduals answer)) (Left "Ground grid retains residual constraints")
  where
    validCell (Var _) = True
    validCell (IntLit n) = n == 0 || n == 1
    validCell _ = False
    groundBinary (IntLit n) = n == 0 || n == 1
    groundBinary _ = False
    groundCell (IntLit n) | n == 0 || n == 1 = Right n
    groundCell other = Left ("Expected a binary ground cell: " ++ show other)

-- Drain even the once continuation so errors/exhaustion cannot hide after an
-- answer. Checkpoint metrics are opt-in and reported separately from timing.
measuredSearch :: Query -> Machine.Checkpoint -> Either String (Search, Machine.Metrics)
measuredSearch query checkpoint = case Machine.resume checkpoint of
  Left err -> Left (show err)
  Right Machine.Finished -> Right ([], Machine.checkpointMetrics checkpoint)
  Right (Machine.Yield item next) -> do
    (remaining, metrics) <- measuredSearch query next
    pure (item : remaining, metrics)

execute :: Engine -> Bool -> Program -> Query -> Either String (QuerySummary, Maybe Machine.Metrics)
execute Reference _ program query = Right (Reference.solveAll program query, Nothing)
execute engine False program query = Right
  (summarizeSearch query (Machine.solveQueryWithBackend (backend engine) program query), Nothing)
execute engine True program query = do
  checkpoint <- either (Left . show) Right (Machine.startMeasuredWithBackend (backend engine) program query)
  (search, metrics) <- measuredSearch query checkpoint
  pure (summarizeSearch query search, Just metrics)

backend :: Engine -> Machine.ExecutionBackend
backend Bytecode = Machine.Bytecode
backend _ = Machine.Interpreted

engineName :: Engine -> String
engineName Native = "native"
engineName Bytecode = "bytecode"
engineName Reference = "reference"

json :: [(String, String)] -> String
json fields = "{" ++ intercalate "," [show key ++ ":" ++ value | (key, value) <- fields] ++ "}"

metricFields :: Machine.Metrics -> [(String, String)]
metricFields metrics =
  [("calls", show (Machine.metricCalls metrics)),
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
   ("max_functors", show (Machine.metricMaxFunctors metrics)),
   ("compiled_activations", show (Machine.metricCompiledActivations metrics)),
   ("bytecode_instructions", show (Machine.metricBytecodeInstructions metrics)),
   ("direct_calls", show (Machine.metricDirectCalls metrics)),
   ("head_instructions", show (Machine.metricHeadInstructions metrics)),
   ("head_cells_avoided", show (Machine.metricHeadCellsAvoided metrics)),
   ("max_activation_registers", show (Machine.metricMaxActivationRegisters metrics)),
   ("body_goals_materialized", show (Machine.metricBodyGoalsMaterialized metrics)),
   ("body_allocation_instructions", show (Machine.metricBodyAllocationInstructions metrics)),
   ("compiled_control_instructions", show (Machine.metricCompiledControlInstructions metrics)),
   ("compiled_cuts", show (Machine.metricCompiledCuts metrics)),
   ("code_cache_hits", show (Machine.metricCodeCacheHits metrics)),
   ("predicate_cache_hits", show (Machine.metricPredicateCacheHits metrics)),
   ("predicate_cache_misses", show (Machine.metricPredicateCacheMisses metrics))]

main :: IO ()
main = do
  arguments <- getArgs
  Options engine phase size bombs budget measured <- either (fail . (++ "\n" ++ usage)) pure (parseOptions arguments)
  source <- readFile "examples/minesweeper.nprolog"
  items <- either fail pure (parseFile source)
  program <- either fail pure (buildChecked [item | item <- items, case item of TLQuery _ -> False; _ -> True])
  let argumentsText = unwords [show size, show size, show bombs, "[window 2 2 2]", "Grid"]
      queryText = "once (" ++ case phase of
        Setup -> "minefield_constraints " ++ argumentsText ++ " Cells)?"
        Ordinary -> "minefield " ++ argumentsText ++ ")?"
  query <- either fail pure (parseQuery queryText)
  _ <- evaluate (length (show program) + length (show query))
  let paths = ["src/Infera/Compile.hs", "src/Infera/Compile/Cache.hs", "src/Infera/Machine/Bytecode.hs",
        "src/Infera/Machine/Control.hs", "src/Infera/Machine/Heap.hs",
        "src/Infera/Machine/Bridge.hs", "src/Infera/Machine/CLP.hs",
        "src/Infera/Machine/Builtins.hs", "src/Infera/Machine/Tail.hs",
        "src/Infera/Machine/Table.hs", "src/Infera/Engine/Reference.hs",
        "src/Infera/Engine.hs", "src/Infera/Engine/Contracts.hs", "src/Infera/Arith.hs",
        "src/Infera/CLP.hs", "src/Infera/Unify.hs", "src/Infera/Program.hs",
        "src/Infera/Infer.hs", "src/Infera/Syntax.hs", "src/Infera/Machine/Trace/Types.hs",
        "examples/minesweeper.nprolog", "bench/machine-minefield.hs"]
  sources <- mapM (\path -> readFile path >>= \contents -> pure (path ++ "\n" ++ contents)) paths
  let fingerprint = show (fingerprintString (concat sources))
      metadata =
        [("engine", show (engineName engine)),
         ("phase", show (if phase == Setup then "setup" else "ordinary" :: String)),
         ("size", show size), ("bombs", show bombs), ("measured", if measured then "true" else "false"),
         ("timeout_seconds", show budget), ("source_fingerprint", show fingerprint),
         ("compiler", show (compilerName ++ "-" ++ showVersion compilerVersion)),
         ("platform", show (arch ++ "-" ++ os)),
         ("scope", show ("loaded checked program; execution+projection+validation; one sample per process" :: String)),
         ("build", show ("runner target -O2; library optimization follows Cabal configuration" :: String))]
      failRun stage status message = do
        putStrLn (json (metadata ++ [("status", show status), ("stage", show stage), ("error", show message)]))
        exitFailure
      limit = round (budget * 1000000)
  _ <- evaluate (length fingerprint)
  -- Native samples compare the exact answer/residual order, outside timing.
  -- The oracle gets the same explicit per-execution budget as the sample.
  oracleResult <- try $ if engine /= Reference then timeout limit $ do
      let oracle = Reference.solveAll program query
      _ <- evaluate (length (show oracle))
      either fail pure (validate phase size bombs oracle)
      pure (Just oracle)
    else pure (Just Nothing)
  oracle <- case oracleResult :: Either IOException (Maybe (Maybe QuerySummary)) of
    Left err -> failRun "oracle" "error" (show err)
    Right Nothing -> failRun "oracle" "timeout" "Reference oracle exceeded budget; no timing emitted"
    Right (Just expected) -> pure expected
  started <- getMonotonicTimeNSec
  attempted <- try $ timeout limit $ do
    (result, metrics) <- either fail pure (execute engine measured program query)
    _ <- evaluate (length (show result) + maybe 0 (length . show) metrics)
    unless (engine /= Bytecode || not measured || case metrics of
      Just counts -> Machine.metricCompiledActivations counts > 0
        && Machine.metricHeadInstructions counts > 0 && Machine.metricHeadCellsAvoided counts > 0
        && Machine.metricBodyGoalsMaterialized counts > 0 && Machine.metricBodyAllocationInstructions counts > 0
      Nothing -> False) (fail "Bytecode minefield did not exercise compiled head matching")
    either fail pure (validate phase size bombs result)
    case oracle of
      Nothing -> pure ()
      Just expected -> unless (result == expected) (fail "Result differs from Reference answer/residual order")
    pure (result, metrics)
  ended <- getMonotonicTimeNSec
  case attempted :: Either IOException (Maybe (QuerySummary, Maybe Machine.Metrics)) of
    Left err -> failRun "execution" "error" (show err)
    Right Nothing -> failRun "execution" "timeout" "Execution exceeded budget; no timing emitted"
    Right (Just (result, metrics)) -> putStrLn $ json (metadata ++
      [("status", show ("ok" :: String)), ("oracle_checked", if engine /= Reference then "true" else "false"),
       ("fully_drained", "true"), ("verified_answers", show (length (summaryAnswers result))),
       ("answer_fingerprint", show (show (fingerprintString (show result)))),
       ("wall_seconds", show (fromIntegral (ended - started) / 1.0e9 :: Double)),
       ("metrics", maybe "null" (json . metricFields) metrics)])
