-- Checked loaded-program comparison for the four Core design improvements.
-- One case and one sample per fresh process. The exact same runner also
-- compiles against the preceding Core API; no implementation counters enter
-- the timed normal Core.solveQuery path.
module Main (main) where

import Control.Exception (IOException, evaluate, try)
import Control.Monad (forM, forM_, unless)
import Data.List (intercalate, nub, sort)
import Data.Version (showVersion)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Fingerprint (fingerprintString)
import GHC.Stats
import Infera hiding (main, solveQuery)
import qualified Infera.Core as Core
import qualified Infera.Engine.Reference as Reference
import System.CPUTime (getCPUTime)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>), takeExtension)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Mem (performGC)
import System.Timeout (timeout)
import Text.Read (readMaybe)

data Options = Options String Int Double

names :: [String]
names = ["controls", "guards", "deep-index", "liveness", "table-cycle",
  "table-cycle240",
  "core-nrev", "core-loop", "core-fib", "core-queens",
  "breadboard-rc", "breadboard-div", "breadboard-tri", "breadboard-wide", "minefield-16"]

usage :: String
usage = "Usage: core-major --case " ++ intercalate "|" names ++
  " [--batch 1..1000000] [--timeout SECONDS] +RTS -T -RTS"

parseOptions :: [String] -> Either String Options
parseOptions = go Nothing Nothing Nothing
  where
    go testCase batch seconds [] = case testCase of
      Nothing -> Left "Missing --case"
      Just chosen -> Right (Options chosen (maybe 1 id batch) (maybe 60 id seconds))
    go Nothing batch seconds ("--case" : value : rest)
      | value `elem` names = go (Just value) batch seconds rest
      | otherwise = Left ("Unknown case: " ++ value)
    go testCase Nothing seconds ("--batch" : value : rest) = case readMaybe value of
      Just count | count > 0 && count <= 1000000 -> go testCase (Just count) seconds rest
      _ -> Left "Batch must be an integer between 1 and 1000000"
    go testCase batch Nothing ("--timeout" : value : rest) = case readMaybe value of
      Just limit | limit > 0 && limit <= 86400 && not (isNaN limit) && not (isInfinite limit)
        && limit <= fromIntegral (maxBound :: Int) / 1000000 ->
        go testCase batch (Just limit) rest
      _ -> Left "Timeout must be positive, finite, and at most 86400 seconds"
    go _ _ _ (flag : _) = Left ("Unknown, duplicate or incomplete option: " ++ flag)

data Model = Exact Term | ReverseThirty | QueensEight | Grid16
  | Ring Integer | Breadboard Integer Integer Int

data Fixture = Fixture String String Model

fixture :: String -> IO Fixture
fixture name = case name of
  "controls" -> pure (Fixture (unlines
    ["<- notable.", "loop 0 Acc Acc.",
     "loop N Acc Result <- N > 0, once ((Picked = N ; Picked = 0)), not (Picked < 0), " ++
       "(Picked > 0 -> Next is Acc + Picked ; Next = Acc), M is N - 1, loop M Next Result."])
    "loop 300 0 Result?" (Exact (IntLit 45150)))
  "guards" -> pure (Fixture (unlines
    ["<- notable.", "classify : nondet (any) (any).",
     "classify N -1 <- N < 0.", "classify N 1 <- N >= 0.",
     "loop 0 Acc Acc.",
     "loop N Acc Result <- N > 0, classify N Sign, Next is Acc + Sign, M is N - 1, loop M Next Result."])
    "loop 5000 0 Result?" (Exact (IntLit 5000)))
  "deep-index" -> pure (Fixture (unlines
    (["<- notable.", "lookup : nondet (any) (any) (any)."] ++
      ["lookup (box (tag " ++ show i ++ ")) " ++ side ++ " " ++ show (i + offset) ++ "."
        | i <- [0 :: Int .. 63], (side, offset) <- [("left", 0), ("right", 64)]] ++
      ["loop 0 Acc Acc.",
       "loop N Acc Result <- N > 0, K is N % 64, lookup (box (tag K)) right Value, " ++
         "Next is Acc + Value, M is N - 1, loop M Next Result."]))
    "loop 5000 0 Result?" (Exact (IntLit (sum [n `mod` 64 + 64 | n <- [1 .. 5000]]))))
  "liveness" -> pure (Fixture (unlines
    ["<- notable.", "pause.", "id X X.",
     "build 0 [].", "build N [N | T] <- N > 0, M is N - 1, build M T.",
     "spin 0.", "spin N <- N > 0, M is N - 1, spin M.",
     "dead_sibling N Result <- build N Junk, id Junk _, pause, spin 90000, Result = done."])
    "dead_sibling 20000 Result?" (Exact (Atom "done")))
  "table-cycle" -> ring 16
  "table-cycle240" -> ring 240
  "core-nrev" -> core "once (bench_nrev 100, range 1 30 L, nrev L Result)?" ReverseThirty
  "core-loop" -> core "once (loop 90000, Result = 90000)?" (Exact (IntLit 90000))
  "core-fib" -> core "once (fib 25 Result)?" (Exact (IntLit 75025))
  "core-queens" -> core "once (queens 8 Result)?" QueensEight
  "minefield-16" -> do
    source <- readFile "examples/minesweeper.nprolog"
    pure (Fixture source "once (minefield 16 16 50 [window 2 2 2] Result)?" Grid16)
  "breadboard-wide" -> bread
    ("Cs = [c p0 r \"1k\" n0 n1 1 1, c p1 r \"1k\" n2 n3 2 2, " ++
     "c p2 r \"1k\" n4 n5 3 3], Wired = [], solve_min Cs Wired 1 16 P Cost?") 1 16 0
  _ | name `elem` ["breadboard-rc", "breadboard-div", "breadboard-tri"] -> do
      let circuit = drop (length "breadboard-") name
      bread ("comps " ++ circuit ++ " Cs, nets Cs Ns, best Cs Ns Wired P Cost?")
        7 11 (if circuit == "tri" then 1 else 0)
  _ -> fail "Unhandled case"
  where
    core query model = do
      source <- readFile "bench/bench.nprolog"
      pure (Fixture source query model)
    bread query lo hi jumpers = do
      source <- readFile "examples/breadboard.nprolog"
      pure (Fixture source query (Breadboard lo hi jumpers))
    ring size = pure (Fixture (unlines
      (["<- notable.", "reach : table."] ++
        ["edge " ++ show i ++ " " ++ show ((i + 1) `mod` size) ++ "." | i <- [0 .. size - 1]] ++
        ["reach X Y <- edge X Y.", "reach X Y <- reach X Z, edge Z Y."]))
      "reach 0 Result?" (Ring size))

data Observation = OAnswer [(String, Term)] [String] [OutputEvent]
  | OError SolveError | OExhausted | OCut Int | ODependency Term
  deriving (Eq, Show)

observe :: Query -> Search -> [Observation]
observe query = map item
  where
    item (Found state) = let answer = projectAnswer query state in
      OAnswer (answerBindings answer) (answerResiduals answer) (answerOutput answer)
    item (BranchError problem) = OError problem
    item BranchExhausted = OExhausted
    item (CutMarker owner) = OCut owner
    item (ConsumedIncomplete key) = ODependency key

-- Each invocation has a unique opaque nonce; only inside this NOINLINE
-- boundary is it reduced to a bounded number of unused query roots. Neither
-- an answer stream nor a checkpoint is passed between invocations.
{-# NOINLINE execute #-}
execute :: Int -> (Program -> Query -> Search) -> Program -> Query -> [Observation]
execute nonce resolver program query = observe query (resolver program shifted)
  where
    shifted = query {queryNVars = queryNVars query + 2 + nonce `mod` 4}

coreSolve :: Program -> Query -> Search
coreSolve program query = case Core.solveQuery program query of
  Nothing -> error "Core refused benchmark query"
  Just items -> items

force :: [Observation] -> IO ()
force observations = () <$ evaluate (length (show observations))

asList :: Term -> Either String [Term]
asList term = case unfoldCons term of
  (values, Nothing) -> Right values
  _ -> Left ("Improper list: " ++ show term)

integer :: Term -> Either String Integer
integer (IntLit value) = Right value
integer other = Left ("Expected ground integer: " ++ show other)

single :: [Observation] -> Either String [(String, Term)]
single [OAnswer bindings [] []] | all (null . termVars . snd) bindings = Right bindings
single _ = Left "Expected one ground answer with no residuals, output, errors or exhaustion"

binding :: String -> [(String, Term)] -> Either String Term
binding name = maybe (Left ("Missing binding: " ++ name)) Right . lookup name

-- Full physical placement fields are checked independently of Infera's
-- scoring predicates and constraint representation.
data Placed = Placed Term Term Integer Integer Integer Integer Integer Integer Integer
  deriving Show

placements :: Term -> Either String [Placed]
placements term = asList term >>= mapM part
  where
    part (Compound "pl" [_, _, _, a, b, _, IntLit row, IntLit col, IntLit half,
        IntLit ha, IntLit hb, IntLit na, IntLit nb]) = Right (Placed a b row col half ha hb na nb)
    part other = Left ("Invalid placement: " ++ show other)

score :: [Placed] -> Integer
score ps = sum [abs (col - 9) | Placed _ _ _ col _ _ _ _ _ <- ps] +
  sum [pair p q | (i, p) <- zip [0 :: Int ..] ps, q <- drop (i + 1) ps]
  where
    pair (Placed a b _ col half _ _ _ _) (Placed c d _ col' half' _ _ _ _) =
      (if half == half' then 0 else 2) +
      (if half == half' && abs (col - col') <= 2 && not (a == c || a == d || b == c || b == d)
        then 4 else 0)

valid :: [Term] -> Integer -> Integer -> [Placed] -> Bool
valid wired lo hi ps = not (null ps) && onTop && all part ps &&
  length holes == length (nub holes) &&
  and [compatible p q | (i, p) <- zip [0 :: Int ..] pins, q <- drop (i + 1) pins]
  where
    onTop = case ps of Placed _ _ _ _ half _ _ _ _ : _ -> half == 0; [] -> False
    part (Placed _ _ row col half ha hb na nb) = row >= 1 && row <= 5 && col >= lo && col <= hi &&
      half `elem` [0, 1] && na == half * 100 + col && nb == na + 1 &&
      ha == na * 10 + row && hb == nb * 10 + row
    holes = concat [[ha, hb] | Placed _ _ _ _ _ ha hb _ _ <- ps]
    pins = concat [[(a, na), (b, nb)] | Placed a b _ _ _ _ _ na nb <- ps]
    compatible (a, na) (b, nb) | a == b = a `elem` wired || na == nb
                             | otherwise = na /= nb

optimum :: Model -> [Observation] -> Either String (Maybe Integer)
optimum (Breadboard lo hi _) actual = do
  bindings <- single actual
  wired <- binding "Wired" bindings >>= asList
  ps <- binding "P" bindings >>= placements
  let candidates =
        [[Placed a b row col half (na * 10 + row) ((na + 1) * 10 + row) na (na + 1)
          | col <- [lo .. hi], half <- if i == 0 then [0] else [0, 1], let na = half * 100 + col]
         | (i, Placed a b row _ _ _ _ _ _) <- zip [0 :: Int ..] ps]
      costs = map score (filter (valid wired lo hi) (sequence candidates))
  case costs of
    [] -> Left "Independent board enumerator found no placement"
    _ -> Right (Just (minimum costs))
optimum _ _ = Right Nothing

independent :: Model -> Maybe Integer -> [Observation] -> Either String ()
independent (Ring size) _ actual = unless
  (actual == [OAnswer [("Result", IntLit n)] [] [] | n <- [1 .. size - 1] ++ [0]])
  (Left "Ordered ring closure differs from independent traversal")
independent model minimumCost actual = do
  bindings <- single actual
  case model of
    Exact expected -> binding "Result" bindings >>= \value ->
      unless (value == expected) (Left "Independent scalar model failed")
    ReverseThirty -> do
      values <- binding "Result" bindings >>= asList
      unless (values == map IntLit [30, 29 .. 1]) (Left "Independent reverse model failed")
    QueensEight -> do
      values <- binding "Result" bindings >>= asList >>= mapM integer
      unless (sort values == [1 .. 8] && and
        [abs (a - b) /= toInteger (j - i) | (i, a) <- zip [0 :: Int ..] values,
          (j, b) <- zip [0 :: Int ..] values, i < j]) (Left "Independent queens model failed")
    Grid16 -> do
      rows <- binding "Result" bindings >>= asList >>= mapM (asList >=> mapM integer)
      unless (length rows == 16 && all ((== 16) . length) rows &&
        all (`elem` [0, 1]) (concat rows) && sum (concat rows) == 50 && and
        [sum [rows !! (y + dy) !! (x + dx) | dy <- [0, 1], dx <- [0, 1]] <= 2
          | y <- [0 .. 14], x <- [0 .. 14]]) (Left "Independent minefield model failed")
    Breadboard lo hi jumpers -> do
      wired <- binding "Wired" bindings >>= asList
      ps <- binding "P" bindings >>= placements
      cost <- binding "Cost" bindings >>= integer
      unless (length wired == jumpers && valid wired lo hi ps && cost == score ps &&
        minimumCost == Just cost) (Left "Independent board validity/optimum model failed")
  where
    (>=>) f g x = f x >>= g

json :: [(String, String)] -> String
json fields = "{" ++ intercalate "," [show key ++ ":" ++ value | (key, value) <- fields] ++ "}"

runtimeSources :: FilePath -> IO [FilePath]
runtimeSources directory = do
  names' <- sort <$> listDirectory directory
  paths <- forM names' $ \name -> do
    let path = directory </> name
    nested <- doesDirectoryExist path
    if nested then runtimeSources path else pure [path | takeExtension path == ".hs"]
  pure (concat paths)

main :: IO ()
main = do
  arguments <- getArgs
  Options name batch seconds <- either (fail . (++ "\n" ++ usage)) pure (parseOptions arguments)
  enabled <- getRTSStatsEnabled
  unless enabled (fail "Enable RTS statistics with +RTS -T -RTS")
  Fixture source queryText model <- fixture name
  items <- either fail pure (parseFile source)
  program <- either fail pure (buildChecked [item | item <- items, case item of TLQuery _ -> False; _ -> True])
  query <- either fail pure (parseQuery queryText)
  _ <- evaluate (length (show program) + length (show query))
  paths <- runtimeSources "src"
  sources <- mapM (\path -> readFile path >>= \contents -> pure (path ++ "\n" ++ contents))
    (paths ++ ["bench/core-major.hs"])
  let fingerprint = show (fingerprintString (concat sources))
      workload = show (fingerprintString (source ++ queryText))
      metadata = [("engine", show ("core" :: String)), ("case", show name),
        ("batch_queries", show batch), ("timeout_seconds", show seconds),
        ("source_fingerprint", show fingerprint), ("workload_fingerprint", show workload),
        ("compiler", show (compilerName ++ "-" ++ showVersion compilerVersion)),
        ("platform", show (arch ++ "-" ++ os)),
        ("scope", show ("loaded checked program; per-query Core compilation, execution, projection and validation; source loading/inference, Reference oracle and Core preflight excluded" :: String))]
      failRun stage status message = do
        putStrLn (json (metadata ++ [("status", show status), ("stage", show stage), ("error", show message)]))
        exitFailure
      within stage action = do
        attempted <- try (timeout (round (seconds * 1000000)) action)
        case attempted of
          Left err -> failRun stage "error" (show (err :: IOException))
          Right Nothing -> failRun stage "timeout" "Explicit time budget exceeded; no timing emitted"
          Right (Just value) -> pure value
  _ <- evaluate (length fingerprint + length workload)
  expected <- within "oracle" $ do
    let oracle = execute 0 Reference.solveQuery program query
    force oracle
    best <- either fail pure (optimum model oracle)
    either fail pure (independent model best oracle)
    pure (oracle, best)
  -- Check that this fixture executes wholly in Core before using its public
  -- normal entry point. This is an untimed preflight, not a timed counter.
  within "core-preflight" $ do
    let shifted = query {queryNVars = queryNVars query + 3}
    outcome <- Core.coreOutcome program shifted
    case outcome of
      Left reason -> fail ("Core fell back: " ++ reason)
      Right _ -> pure ()
  performGC
  before <- getRTSStats
  wall0 <- getMonotonicTimeNSec
  cpu0 <- getCPUTime
  actual <- within "execution" $ do
    let check nonce = do
          let result = execute nonce coreSolve program query
          force result
          either fail pure (independent model (snd expected) result)
          unless (result == fst expected) (fail "Complete ordered stream differs from Reference")
          pure result
    forM_ [1 .. batch - 1] $ \nonce -> () <$ check nonce
    check batch
  cpu1 <- getCPUTime
  wall1 <- getMonotonicTimeNSec
  timedStats <- getRTSStats
  -- Include the unfinished nursery in allocation accounting. Its forced GC
  -- is outside CPU/wall timing; process residency also includes setup/oracle.
  performGC
  after <- getRTSStats
  let wall = fromIntegral (wall1 - wall0) / 1.0e9 :: Double
      cpu = fromIntegral (cpu1 - cpu0) / 1.0e12 :: Double
      allocated = allocated_bytes after - allocated_bytes before
      answers = length [() | OAnswer _ _ _ <- actual]
  putStrLn (json (metadata ++
    [("status", show ("ok" :: String)), ("fully_drained", "true"),
     ("oracle_checked", "true"), ("independent_checked", "true"),
     ("untimed_core_preflight_queries", "1"), ("timed_instruction_counters", "false"),
     ("fresh_query_state", "true"),
     ("query_base_policy", show ("unique NOINLINE nonce; unused query roots cycle 2..5" :: String)),
     ("verified_answers", show answers), ("verified_answers_total", show (answers * batch)),
     ("answer_fingerprint", show (show (fingerprintString (show actual)))),
     ("wall_seconds", show wall), ("cpu_seconds", show cpu),
     ("per_query_wall_seconds", show (wall / fromIntegral batch)),
     ("per_query_cpu_seconds", show (cpu / fromIntegral batch)),
     ("execution_allocated_bytes", show allocated),
     ("per_query_allocated_bytes", show (fromIntegral allocated / fromIntegral batch :: Double)),
     ("timed_gc_count", show (gcs timedStats - gcs before)),
     ("timed_gc_cpu_seconds", show (fromIntegral (gc_cpu_ns timedStats - gc_cpu_ns before) / 1.0e9 :: Double)),
     ("process_max_live_bytes", show (max_live_bytes after)),
     ("final_live_bytes", show (gcdetails_live_bytes (gc after))),
     ("allocation_scope", show ("timed batch plus final RTS sampling/GC bookkeeping; final forced GC excluded from timing" :: String)),
     ("residency_scope", show ("whole process including Reference oracle and untimed Core preflight; this is not a Core heap-live counter" :: String))]))
