-- Build with Cabal's machine-breadboard benchmark target. This measures
-- already-loaded program execution, including projection and validation,
-- rather than CLI startup, parsing, or program inference.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_, unless)
import Data.List (intercalate, nub, sort)
import Data.Version (showVersion)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Fingerprint (fingerprintString)
import Infera hiding (main)
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Timeout (timeout)
import Text.Read (readMaybe)

data Options = Options Int (Maybe String) (Maybe String)

usage :: String
usage = "Usage: machine-breadboard [--batch 1..1000000] [--engine reference|machine|bytecode] [--case rc|div|tri|wide-disconnected]"

parseOptions :: [String] -> Either String Options
parseOptions = parse Nothing Nothing Nothing
  where
    parse batch engine testCase [] = Right (Options (maybe 1 id batch) engine testCase)
    parse Nothing engine testCase ("--batch" : value : rest) = case readMaybe value of
      Just count | count > 0 && count <= 1000000 -> parse (Just count) engine testCase rest
      _ -> Left "Batch size must be an integer between 1 and 1000000"
    parse batch Nothing testCase ("--engine" : value : rest)
      | value `elem` ["reference", "machine", "bytecode"] = parse batch (Just value) testCase rest
      | otherwise = Left ("Unknown engine: " ++ value)
    parse batch engine Nothing ("--case" : value : rest)
      | value `elem` ["rc", "div", "tri", "wide-disconnected"] = parse batch engine (Just value) rest
      | otherwise = Left ("Unknown case: " ++ value)
    parse _ _ _ [flag] | flag `elem` ["--batch", "--engine", "--case"] =
      Left ("Missing value after " ++ flag)
    parse _ _ _ (flag : _) = Left ("Duplicate or unknown option: " ++ flag)

data Case = Case String String Integer Integer Int

cases :: [Case]
cases =
  [Case circuit ("comps " ++ circuit ++ " Cs, nets Cs Ns, best Cs Ns Wired P Cost?") 7 11
      (if circuit == "tri" then 1 else 0) | circuit <- ["rc", "div", "tri"]] ++
  [Case "wide-disconnected"
    ("Cs = [c p0 r \"1k\" n0 n1 1 1, c p1 r \"1k\" n2 n3 2 2, " ++
     "c p2 r \"1k\" n4 n5 3 3], Wired = [], solve_min Cs Wired 1 16 P Cost?") 1 16 0]

data Placed = Placed Term Term Term Integer Integer Integer Integer Integer Integer Integer
  deriving (Eq, Ord, Show)

asList :: Term -> Either String [Term]
asList term = case unfoldCons term of
  (values, Nothing) -> Right values
  _ -> Left ("Expected a proper list: " ++ show term)

placements :: Term -> Either String [Placed]
placements term = asList term >>= mapM part
  where
    part (Compound "pl" [name, _, _, a, b, _, IntLit row, IntLit col, IntLit half,
                         IntLit ha, IntLit hb, IntLit na, IntLit nb]) =
      Right (Placed name a b row col half ha hb na nb)
    part other = Left ("Expected a ground placement: " ++ show other)

costModel :: [Placed] -> Integer
costModel ps = sum [abs (col - 9) | Placed _ _ _ _ col _ _ _ _ _ <- ps] +
  sum [pair p q | (i, p) <- zip [0 :: Int ..] ps, q <- drop (i + 1) ps]
  where
    pair (Placed _ a b _ col half _ _ _ _) (Placed _ c d _ col' half' _ _ _ _) =
      (if half == half' then 0 else 2) +
      (if half == half' && abs (col - col') <= 2 && not (a == c || a == d || b == c || b == d)
        then 4 else 0)

valid :: [Term] -> Integer -> Integer -> [Placed] -> Bool
valid wired lo hi ps = not (null ps) && top && all part ps &&
  length holes == length (nub holes) &&
  and [compatible x y | (i, x) <- zip [0 :: Int ..] pins, y <- drop (i + 1) pins]
  where
    top = case ps of Placed _ _ _ _ _ half _ _ _ _ : _ -> half == 0; [] -> False
    part (Placed _ _ _ row col half ha hb na nb) =
      row >= 1 && row <= 5 && col >= lo && col <= hi && half `elem` [0, 1] &&
      na == half * 100 + col && nb == na + 1 && ha == na * 10 + row && hb == nb * 10 + row
    holes = concat [[ha, hb] | Placed _ _ _ _ _ _ ha hb _ _ <- ps]
    pins = concat [[(a, na), (b, nb)] | Placed _ a b _ _ _ _ _ na nb <- ps]
    compatible (a, na) (b, nb) | a == b = a `elem` wired || na == nb
                             | otherwise = na /= nb

independentCosts :: [Term] -> Integer -> Integer -> [Placed] -> [Integer]
independentCosts wired lo hi ps = map costModel (filter (valid wired lo hi) (sequence candidates))
  where
    candidates =
      [[Placed name a b row col half (na * 10 + row) ((na + 1) * 10 + row) na (na + 1)
        | col <- [lo .. hi], half <- if i == 0 then [0] else [0, 1], let na = half * 100 + col]
       | (i, Placed name a b row _ _ _ _ _ _) <- zip [0 :: Int ..] ps]

lookupBinding :: String -> Answer -> Either String Term
lookupBinding name answer = maybe (Left ("Missing binding " ++ name)) Right (lookup name (answerBindings answer))

-- Compute this independent minimum once per case, outside all timed samples.
expectedCost :: Case -> QuerySummary -> Either String Integer
expectedCost (Case _ _ lo hi _) summary = do
  answer <- case summaryAnswers summary of [result] -> Right result; _ -> Left "Expected exactly one answer"
  wired <- lookupBinding "Wired" answer >>= asList
  ps <- lookupBinding "P" answer >>= placements
  case independentCosts wired lo hi ps of
    [] -> Left "Independent grid enumerator found no valid placement"
    costs -> Right (minimum costs)

validate :: Case -> Integer -> QuerySummary -> Either String ()
validate (Case name _ lo hi jumperCount) optimum summary = do
  unless (null (summaryErrors summary)) (Left (name ++ ": " ++ show (summaryErrors summary)))
  unless (not (summaryExhausted summary)) (Left (name ++ ": resolution exhausted"))
  answer <- case summaryAnswers summary of [result] -> Right result; _ -> Left (name ++ ": expected one answer")
  unless (all (null . termVars . snd) (answerBindings answer)) (Left (name ++ ": nonground answer"))
  wired <- lookupBinding "Wired" answer >>= asList
  unless (length wired == jumperCount) (Left (name ++ ": unexpected jumper count"))
  ps <- lookupBinding "P" answer >>= placements
  cost <- lookupBinding "Cost" answer >>= \term -> case term of
    IntLit value -> Right value
    _ -> Left (name ++ ": nonground cost")
  unless (valid wired lo hi ps) (Left (name ++ ": invalid physical placement"))
  unless (cost == costModel ps && cost == optimum) (Left (name ++ ": incorrect optimum"))

observe :: QuerySummary -> [([(String, Term)], [String], [OutputEvent])]
observe = map (\answer -> (answerBindings answer, answerResiduals answer, answerOutput answer)) . summaryAnswers

-- A distinct unused fresh-variable base prevents repeated pure solver
-- applications from sharing an evaluated result across samples. Both engines
-- receive the same bases; named variables and the program are unchanged.
{-# NOINLINE execute #-}
execute :: Int -> (Program -> Query -> Search) -> Program -> Query -> QuerySummary
execute serial resolver program query =
  summarizeSearch query (resolver program (query {queryNVars = queryNVars query + serial}))

-- Only batched samples use cyclic bases. The unique nonce remains opaque to
-- the loop, so every iteration starts a fresh query without unbounded roots.
{-# NOINLINE executeBounded #-}
executeBounded :: Int -> (Program -> Query -> Search) -> Program -> Query -> QuerySummary
executeBounded nonce = execute (2 + nonce `mod` 4)

checkedRun :: Int -> Int -> (Program -> Query -> Search) -> Program -> Query -> Case -> Integer -> QuerySummary -> IO (Double, Double)
checkedRun serial batch resolver program query testCase optimum expected = do
  wallStart <- getMonotonicTimeNSec
  cpuStart <- getCPUTime
  completed <- timeout 30000000 $ do
    let checkedResult result = do
          _ <- evaluate (length (show result))
          either fail pure (validate testCase optimum result)
          unless (observe result == observe expected) (fail "Result differs from reference placement/order")
    if batch == 1 then checkedResult (execute serial resolver program query) else
      forM_ [0 .. batch - 1] $ \index ->
        checkedResult (executeBounded (serial * batch + index) resolver program query)
  cpuEnd <- getCPUTime
  wallEnd <- getMonotonicTimeNSec
  case completed of
    Nothing -> fail "Breadboard benchmark exceeded 30 seconds; no timing emitted"
    Just () -> pure (fromIntegral (wallEnd - wallStart) / 1.0e9, fromIntegral (cpuEnd - cpuStart) / 1.0e12)

median :: [Double] -> Double
median values = sort values !! (length values `div` 2)

compiledProbe :: Program -> Query -> Case -> Integer -> QuerySummary -> IO ()
compiledProbe program query testCase@(Case name _ _ _ _) optimum expected = do
  completed <- timeout 30000000 $ do
    checkpoint <- either (fail . show) pure (Machine.startMeasuredWithBackend Machine.Bytecode program
      (query {queryNVars = queryNVars query + 5}))
    (search, metrics) <- either fail pure (drain checkpoint)
    let actual = summarizeSearch query search
    _ <- evaluate (length (show actual))
    either fail pure (validate testCase optimum actual)
    unless (observe actual == observe expected) (fail "Compiled probe differs from reference placement/order")
    unless (Machine.metricCompiledActivations metrics > 0
      && Machine.metricHeadInstructions metrics > 0
      && Machine.metricBodyGoalsMaterialized metrics > 0
      && Machine.metricBodyAllocationInstructions metrics > 0)
      (fail "Compiled breadboard probe did not exercise incremental allocation")
    pure metrics
  case completed of
    Nothing -> fail (name ++ ": compiled breadboard probe exceeded 30 seconds")
    Just metrics -> putStrLn (intercalate " "
      ["# compiled_probe", "case=" ++ name,
       "compiled_activations=" ++ show (Machine.metricCompiledActivations metrics),
       "head_instructions=" ++ show (Machine.metricHeadInstructions metrics),
       "body_goals_materialized=" ++ show (Machine.metricBodyGoalsMaterialized metrics),
       "body_allocation_instructions=" ++ show (Machine.metricBodyAllocationInstructions metrics),
       "max_activation_registers=" ++ show (Machine.metricMaxActivationRegisters metrics),
       "code_cache_hits=" ++ show (Machine.metricCodeCacheHits metrics),
       "predicate_cache_hits=" ++ show (Machine.metricPredicateCacheHits metrics),
       "predicate_cache_misses=" ++ show (Machine.metricPredicateCacheMisses metrics),
       "fully_drained=true", "timed=false"]) >>
      -- Show includes new runtime fields without requiring their accessors in
      -- an older baseline. Matched-stage orchestration checks new path counters.
      putStrLn ("# compiled_metrics case=" ++ name ++ " value=" ++ show metrics)
  where
    drain checkpoint = case Machine.resume checkpoint of
      Left problem -> Left (show problem)
      Right Machine.Finished -> Right ([], Machine.checkpointMetrics checkpoint)
      Right (Machine.Yield item next) -> do
        (remaining, metrics) <- drain next
        pure (item : remaining, metrics)

main :: IO ()
main = do
  arguments <- getArgs
  Options batch selectedEngine selectedCase <- either (fail . (++ "\n" ++ usage)) pure (parseOptions arguments)
  source <- readFile "examples/breadboard.nprolog"
  items <- either fail pure (parseFile source)
  program <- either fail pure (buildChecked [item | item <- items, case item of TLQuery _ -> False; _ -> True])
  -- Force the parsed/checked program before the first timed execution.
  _ <- evaluate (length (show program))
  let sourcePaths = ["src/Infera/Compile.hs", "src/Infera/Compile/Cache.hs", "src/Infera/Machine/Bytecode.hs",
        "src/Infera/Machine/Control.hs", "src/Infera/Machine/Tail.hs", "src/Infera/Machine/CLP.hs",
        "src/Infera/Machine/Bridge.hs", "src/Infera/Machine/Heap.hs", "src/Infera/Engine.hs", "src/Infera/Engine/Reference.hs",
        "src/Infera/Machine/Builtins.hs", "src/Infera/Machine/Table.hs", "src/Infera/Machine/Trace/Types.hs",
        "src/Infera/Engine/Contracts.hs", "src/Infera/CLP.hs",
        "src/Infera/Syntax.hs", "src/Infera/Unify.hs", "src/Infera/Arith.hs", "src/Infera/Program.hs",
        "src/Infera/Infer.hs", "src/Infera/Purity.hs", "src/Infera/Diagnostic.hs",
        "examples/breadboard.nprolog", "bench/machine-breadboard.hs"]
  sources <- mapM (\path -> readFile path >>= \contents -> pure (path, contents)) sourcePaths
  putStrLn ("# source-fingerprint=" ++ show (fingerprintString (concatMap (\(path, contents) -> path ++ "\n" ++ contents) sources)))
  putStrLn ("# compiler=" ++ compilerName ++ "-" ++ showVersion compilerVersion ++ " platform=" ++ arch ++ "-" ++ os)
  putStrLn "# scope=loaded checked program; each selected engine warmed by one checked query; execution+projection+validation; compiled probe after all timed batches per case; no parsing or CLI startup"
  putStrLn "# build=runner target -O2; library optimization follows Cabal configuration (run with -O2)"
  putStrLn "# warmups=1 checked query before timing; runs=3 timeout_seconds=30 per timed batch; no_timing_threshold"
  putStrLn ("# phase=warm batch_queries=" ++ show batch ++ " timed_instruction_counters=false query_base_policy=" ++
    (if batch == 1 then "historical fresh_unused_variables=1..4" else "unique NOINLINE nonce; unused roots cycle 2..5"))
  putStrLn ("# selected_engine=" ++ maybe "all" id selectedEngine ++ " selected_case=" ++ maybe "all" id selectedCase)
  putStrLn "# existing wall/cpu columns are per-query averages; appended batch columns are total batch durations"
  putStrLn "engine\tcase\tmedian_wall_seconds\tmedian_cpu_seconds\twall_samples\tcpu_samples\tmedian_batch_wall_seconds\tmedian_batch_cpu_seconds\tbatch_wall_samples\tbatch_cpu_samples"
  forM_ [testCase | testCase@(Case name _ _ _ _) <- cases,
    maybe True (== name) selectedCase] $ \testCase@(Case name text _ _ _) -> do
    query <- either fail pure (parseQuery text)
    let expected = execute 0 Reference.solveQuery program query
    initial <- timeout 30000000 (evaluate (length (show expected)))
    case initial of Nothing -> fail (name ++ ": reference validation timed out"); Just _ -> pure ()
    optimum <- either fail pure (expectedCost testCase expected)
    either fail pure (validate testCase optimum expected)
    putStrLn ("# workload_fingerprint case=" ++ name ++ " value=" ++
      show (fingerprintString (source ++ text)))
    putStrLn ("# answer_fingerprint case=" ++ name ++ " value=" ++
      show (fingerprintString (show (observe expected))))
    forM_ [(engine, resolver) |
      (engine, resolver) <- [("reference", Reference.solveQuery), ("machine", Machine.solveQuery),
        ("bytecode", Machine.solveQueryWithBackend Machine.Bytecode)],
      maybe True (== engine) selectedEngine] $ \(engine, resolver) -> do
      _ <- checkedRun 1 1 resolver program query testCase optimum expected
      samples <- forM [2 .. 4] $ \serial -> checkedRun serial batch resolver program query testCase optimum expected
      let batchWalls = map fst samples
          batchCpus = map snd samples
          walls = map (/ fromIntegral batch) batchWalls
          cpus = map (/ fromIntegral batch) batchCpus
      putStrLn (intercalate "\t" [engine, name, show (median walls), show (median cpus), show walls, show cpus,
        show (median batchWalls), show (median batchCpus), show batchWalls, show batchCpus])
    compiledProbe program query testCase optimum expected
