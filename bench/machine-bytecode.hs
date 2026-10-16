-- Compare the opt-in first-order compiler with both existing execution paths.
-- All samples drain and validate the complete ordered search stream. Programs
-- are parsed/checked before timing; per-query compilation stays inside timing.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_, unless)
import Data.List (intercalate, sort)
import Data.Version (showVersion)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Fingerprint (fingerprintString)
import Infera hiding (main)
import qualified Infera.Compile as Compile
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import System.CPUTime (getCPUTime)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Timeout (timeout)

data Model = SumTo Integer | Entries Int | Done
data Case = Case String String String Model

cases :: [Case]
cases =
  [ Case "helper-dispatch-10000" fixture "loop 10000 0 Result?" (SumTo 10000),
    Case "structured-list-300" fixture "build 300 [] Result?" (Entries 300),
    Case "structured-head-10000" fixture "head_loop 10000 0 Result?" (SumTo 10000),
    Case "early-fail-body-2000" failureFixture "(huge _ ; Result = done)?" Done
  ]

-- A separate program avoids adding this large cold compiler workload to the
-- other cases. The fallback answer exposes metrics accumulated before failure.
failureFixture :: String
failureFixture = unlines
  [ "<- notable.",
    "sink _ _.",
    "huge Result <- fail, " ++ intercalate ", "
      ["sink (entry " ++ show n ++ " (pair " ++ show n ++ " " ++ show n
        ++ ") [" ++ intercalate ", " (replicate 3 (show n)) ++ "]) Result"
      | n <- [1 .. 2000 :: Int]] ++ "."
  ]

fixture :: String
fixture = unlines
  [ "<- notable.",
    "step N Acc M Next <- M is N - 1, Next is Acc + N.",
    "loop 0 Acc Acc.",
    "loop N Acc Result <- N > 0, step N Acc M Next, loop M Next Result.",
    "prepend N Acc [entry N (pair N N) [N, N, N] | Acc].",
    "build 0 Acc Acc.",
    "build N Acc Result <- N > 0, M is N - 1, prepend N Acc Next, build M Next Result.",
    "read_node (node (pair X X) [X, X, X] (tag X X X)) X.",
    "head_loop 0 Acc Acc.",
    "head_loop N Acc Result <- N > 0, read_node (node (pair N N) [N, N, N] (tag N N N)) Value, M is N - 1, Next is Acc + Value, head_loop M Next Result."
  ]

-- Keep errors, exhaustion and non-answer items in their original positions.
-- These fixtures are ground integer programs, so Term equality is exact and
-- no normalization can conceal alias or floating-point discrepancies.
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
    item (Found state) =
      let answer = projectAnswer query state
       in AnswerObservation (answerBindings answer) (answerResiduals answer) (answerOutput answer)
    item (BranchError problem) = ErrorObservation problem
    item BranchExhausted = ExhaustionObservation
    item (CutMarker owner) = CutObservation owner
    item (ConsumedIncomplete key) = IncompleteObservation key

independent :: Model -> [Observation]
independent model = [AnswerObservation [("Result", result)] [] []]
  where
    result = case model of
      SumTo count -> IntLit (div (count * (count + 1)) 2)
      Entries count -> mkList
        [ Compound "entry" [IntLit value, Compound "pair" [IntLit value, IntLit value],
            mkList (replicate 3 (IntLit value)) Nothing]
        | value <- map toInteger [1 .. count]
        ] Nothing
      Done -> Atom "done"

-- Distinct unused logical-variable bases prevent pure applications from
-- sharing an already evaluated search across samples. Named variables stay
-- unchanged, and every engine receives exactly the same bases.
{-# NOINLINE execute #-}
execute :: Int -> (Program -> Query -> Search) -> Program -> Query -> [Observation]
execute serial resolver program query = observe query
  (resolver program (query {queryNVars = queryNVars query + serial}))

budgetMicroseconds :: Int
budgetMicroseconds = 30000000

forceObservations :: [Observation] -> IO ()
forceObservations observations = do
  _ <- evaluate (length (show observations))
  pure ()

validate :: Case -> [Observation] -> [Observation] -> IO ()
validate (Case name _ _ model) expected actual = do
  unless (actual == independent model) (fail (name ++ ": independent result model failed"))
  unless (actual == expected) (fail (name ++ ": ordered answer/residual/output/error/exhaustion stream differs from Reference"))

checkedRun :: Int -> String -> (Program -> Query -> Search) -> Program -> Query
  -> Case -> [Observation] -> IO (Double, Double)
checkedRun serial engine resolver program query testCase@(Case name _ _ _) expected = do
  wallStart <- getMonotonicTimeNSec
  cpuStart <- getCPUTime
  completed <- timeout budgetMicroseconds $ do
    let actual = execute serial resolver program query
    forceObservations actual
    validate testCase expected actual
  cpuEnd <- getCPUTime
  wallEnd <- getMonotonicTimeNSec
  case completed of
    Nothing -> fail (engine ++ "/" ++ name ++ ": exceeded explicit 30 second budget; no timing emitted")
    Just () -> pure (fromIntegral (wallEnd - wallStart) / 1.0e9,
      fromIntegral (cpuEnd - cpuStart) / 1.0e12)

drain :: Machine.Checkpoint -> Either Heap.HeapError (Search, Machine.Metrics)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], Machine.checkpointMetrics checkpoint)
    Machine.Yield item next -> do
      (remaining, metrics) <- drain next
      pure (item : remaining, metrics)

-- Sampling is opt-in and outside all timing rows. A positive counter check
-- prevents a successful all-fallback benchmark from being called bytecode.
compiledProbe :: Program -> Query -> Case -> [Observation] -> IO ()
compiledProbe program query testCase@(Case name _ _ model) expected = do
  completed <- timeout budgetMicroseconds $ do
    checkpoint <- either (fail . show) pure
      (Machine.startMeasuredWithBackend Machine.Bytecode program
        (query {queryNVars = queryNVars query + 5}))
    (search, metrics) <- either (fail . show) pure (drain checkpoint)
    let actual = observe query search
    forceObservations actual
    validate testCase expected actual
    unless (Machine.metricCompiledActivations metrics > 0
      && Machine.metricBytecodeInstructions metrics > 0
      && Machine.metricHeadInstructions metrics > 0
      && Machine.metricHeadCellsAvoided metrics > 0)
      (fail (name ++ ": compiled head matching was not exercised"))
    case model of
      Done -> unless (Machine.metricBodyGoalsMaterialized metrics == 1
        && Machine.metricMaxHeapCells metrics < 64
        && Machine.metricMaxTasks metrics <= 4
        && Machine.metricMaxActivationRegisters metrics <= 2)
          (fail (name ++ ": unreachable body goals were allocated"))
      _ -> unless (Machine.metricDirectCalls metrics > 0)
        (fail (name ++ ": direct dispatch was not exercised"))
    _ <- evaluate (length (show metrics))
    pure metrics
  case completed of
    Nothing -> fail (name ++ ": untimed compiled probe exceeded explicit 30 second budget")
    Just metrics -> putStrLn (intercalate " "
      [ "# compiled_probe", "case=" ++ name,
        "compiled_activations=" ++ show (Machine.metricCompiledActivations metrics),
        "bytecode_instructions=" ++ show (Machine.metricBytecodeInstructions metrics),
        "direct_calls=" ++ show (Machine.metricDirectCalls metrics),
        "head_instructions=" ++ show (Machine.metricHeadInstructions metrics),
        "head_cells_avoided=" ++ show (Machine.metricHeadCellsAvoided metrics),
        "max_activation_registers=" ++ show (Machine.metricMaxActivationRegisters metrics),
        "body_goals_materialized=" ++ show (Machine.metricBodyGoalsMaterialized metrics),
        "body_allocation_instructions=" ++ show (Machine.metricBodyAllocationInstructions metrics),
        "max_heap_cells=" ++ show (Machine.metricMaxHeapCells metrics),
        "max_tasks=" ++ show (Machine.metricMaxTasks metrics),
        "fully_drained=true", "timed=false"
      ])

median :: [Double] -> Double
median values = sort values !! div (length values) 2

main :: IO ()
main = do
  let paths =
        [ "src/Infera/Compile.hs", "src/Infera/Machine/Bytecode.hs",
          "src/Infera/Machine/Control.hs", "src/Infera/Machine/Heap.hs",
          "src/Infera/Machine/Bridge.hs", "src/Infera/Machine/CLP.hs",
          "src/Infera/Machine/Builtins.hs", "src/Infera/Machine/Tail.hs",
          "src/Infera/Machine/Table.hs", "src/Infera/Machine/Trace/Types.hs",
          "src/Infera/Engine.hs", "src/Infera/Engine/Reference.hs",
          "src/Infera/Engine/Contracts.hs", "src/Infera/Arith.hs",
          "src/Infera/CLP.hs", "src/Infera/Unify.hs", "src/Infera/Program.hs",
          "src/Infera/Infer.hs", "src/Infera/Purity.hs", "src/Infera/Diagnostic.hs",
          "src/Infera/Syntax.hs", "bench/machine-bytecode.hs"
        ]
  sources <- mapM (\path -> readFile path >>= \contents -> pure (path ++ "\n" ++ contents)) paths
  let fingerprint = show (fingerprintString (concat sources))
  _ <- evaluate (length fingerprint)
  putStrLn ("# source-fingerprint=" ++ fingerprint)
  putStrLn ("# compiler=" ++ compilerName ++ "-" ++ showVersion compilerVersion ++ " platform=" ++ arch ++ "-" ++ os)
  putStrLn "# scope=loaded case-specific checked program; cold per-query compilation/cache construction+execution+projection+validation; no parsing or CLI startup"
  putStrLn "# build=runner target -O2; library optimization follows Cabal configuration (run with -O2)"
  putStrLn "# warmups=1 runs=3 timeout_seconds=30 fresh_unused_variables=1..4 measured_probe=5 normal_counters=false no_timing_threshold"
  putStrLn "# head counters describe accepted heads; failed head work is excluded; body counters count reached materializations"
  putStrLn "engine\tcase\tmedian_wall_seconds\tmedian_cpu_seconds\twall_samples\tcpu_samples"
  forM_ cases $ \testCase@(Case name source text model) -> do
    items <- either fail pure (parseFile source)
    program <- either fail pure (buildChecked items)
    _ <- evaluate (length (show program))
    query <- either fail pure (parseQuery text)
    putStrLn ("# workload_fingerprint case=" ++ name ++ " value=" ++
      show (fingerprintString (source ++ text ++ show (independent model))))
    let expected = execute 0 Reference.solveQuery program query
    initial <- timeout budgetMicroseconds $ do
      forceObservations expected
      unless (expected == independent model) (fail (name ++ ": Reference failed independent result model"))
    case initial of
      Nothing -> fail (name ++ ": Reference oracle exceeded explicit 30 second budget; no timing emitted")
      Just () -> pure ()
    compiledProbe program query testCase expected
    forM_
      [ ("reference", Reference.solveQuery),
        ("interpreted", Machine.solveQueryWithBackend Machine.Interpreted),
        ("bytecode", Machine.solveQueryWithBackend Machine.Bytecode)
      ] $ \(engine, resolver) -> do
        _ <- checkedRun 1 engine resolver program query testCase expected
        samples <- forM [2 .. 4] $ \serial ->
          checkedRun serial engine resolver program query testCase expected
        let walls = map fst samples
            cpus = map snd samples
        putStrLn (intercalate "\t"
          [engine, name, show (median walls), show (median cpus), show walls, show cpus])
    let plans = [code | TLClause clause <- items, Just code <- [Compile.compileClause clause]]
    putStrLn (intercalate " "
      [ "# register_plan", "case=" ++ name, "scope=all_supported_case_clauses",
        "unshared_slots=" ++ show (sum (map Compile.codeUnsharedSlotCount plans)),
        "pooled_slots=" ++ show (sum (map Compile.codeSlotCount plans)),
        "max_body_temporary_registers=" ++ show
          (maximum (0 : [Compile.goalRegisterCount goal | code <- plans, goal <- Compile.codeGoals code])),
        "timed=false"
      ])
