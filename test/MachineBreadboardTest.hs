{-# LANGUAGE OverloadedStrings #-}

-- Acceptance for the experimental heap/control/CLP path. The small grid
-- enumerator below has no dependency on Infera's constraints or score code.
module MachineBreadboardTest (machineBreadboardGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.List (intercalate, nub, sort)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import System.Timeout (timeout)

loadBreadboard :: PropertyT IO Program
loadBreadboard = do
  source <- evalIO (readFile "examples/breadboard.nprolog")
  items <- evalEither (parseFile source)
  evalEither (buildChecked [item | item <- items, case item of TLQuery _ -> False; _ -> True])

solveWith :: (Program -> Query -> Search) -> Program -> String -> PropertyT IO QuerySummary
solveWith resolver program text = do
  annotate text
  query <- evalEither (parseQuery text)
  let result = summarizeSearch query (resolver program query)
  completed <- evalIO (timeout 30000000 (evaluate (length (show result))))
  case completed of
    Nothing -> annotate "Breadboard query exceeded 30 seconds" >> failure
    Just _ -> success
  summaryErrors result === []
  summaryExhausted result === False
  pure result

native, reference :: Program -> String -> PropertyT IO QuerySummary
native = solveWith Machine.solveQuery
reference = solveWith Reference.solveQuery

binding :: String -> Answer -> PropertyT IO Term
binding name answer = maybe (annotateShow answer >> failure) pure (lookup name (answerBindings answer))

integer :: Term -> PropertyT IO Integer
integer (IntLit value) = pure value
integer other = annotateShow other >> failure

list :: Term -> PropertyT IO [Term]
list term = case unfoldCons term of
  (values, Nothing) -> pure values
  _ -> annotateShow term >> failure

-- Include the component identity, row and both derived hole/node fields in
-- validation: a low score alone would not prove a physically valid board.
data Placed = Placed Term Term Term Integer Integer Integer Integer Integer Integer Integer
  deriving (Eq, Ord, Show)

placed :: Term -> PropertyT IO [Placed]
placed term = list term >>= mapM part
  where
    part (Compound "pl" [name, _, _, a, b, _, IntLit row, IntLit col, IntLit half,
                         IntLit holeA, IntLit holeB, IntLit nodeA, IntLit nodeB]) =
      pure (Placed name a b row col half holeA holeB nodeA nodeB)
    part other = annotateShow other >> failure

scoreModel :: [Placed] -> Integer
scoreModel parts = sum [abs (col - 9) | Placed _ _ _ _ col _ _ _ _ _ <- parts] +
  sum [pair p q | (i, p) <- zip [0 :: Int ..] parts, q <- drop (i + 1) parts]
  where
    pair (Placed _ a b _ col half _ _ _ _) (Placed _ c d _ col' half' _ _ _ _) =
      (if half == half' then 0 else 2) +
      (if half == half' && abs (col - col') <= 2 && not (a == c || a == d || b == c || b == d)
        then 4 else 0)

validGrid :: [Term] -> Integer -> Integer -> [Placed] -> Bool
validGrid wired lo hi parts = not (null parts) && firstOnTop &&
  all validPart parts && length holes == length (nub holes) &&
  and [compatible p q | (i, p) <- zip [0 :: Int ..] pins, q <- drop (i + 1) pins]
  where
    firstOnTop = case parts of Placed _ _ _ _ _ half _ _ _ _ : _ -> half == 0; [] -> False
    validPart (Placed _ _ _ row col half ha hb na nb) =
      row >= 1 && row <= 5 && col >= lo && col <= hi && half `elem` [0, 1] &&
      na == half * 100 + col && nb == na + 1 && ha == na * 10 + row && hb == nb * 10 + row
    holes = concat [[ha, hb] | Placed _ _ _ _ _ _ ha hb _ _ <- parts]
    pins = concat [[(a, na), (b, nb)] | Placed _ a b _ _ _ _ _ na nb <- parts]
    compatible (a, na) (b, nb)
      | a == b = a `elem` wired || na == nb
      | otherwise = na /= nb

coordinates :: [Placed] -> [(Term, Integer, Integer, Integer)]
coordinates parts = [(name, row, col, half) | Placed name _ _ row col half _ _ _ _ <- parts]

scored :: Answer -> PropertyT IO (Integer, [(Term, Integer, Integer, Integer)])
scored answer = do
  cost <- binding "Cost" answer >>= integer
  ps <- binding "P" answer >>= placed
  cost === scoreModel ps
  pure (cost, coordinates ps)

-- Standard acceptance queries are ground. Compare all public bindings,
-- residuals and ordered output while ignoring internal answer-name maps.
observations :: QuerySummary -> [([(String, Term)], [String], [OutputEvent])]
observations = map (\answer -> (answerBindings answer, answerResiduals answer, answerOutput answer)) . summaryAnswers

groundAnswer :: Answer -> PropertyT IO ()
groundAnswer answer = forM_ (answerBindings answer) $ \(_, term) -> termVars term === []

one :: QuerySummary -> PropertyT IO Answer
one summary = case summaryAnswers summary of
  [answer] -> pure answer
  other -> annotateShow other >> failure

prop_shipped_circuits :: Property
prop_shipped_circuits = withTests 1 . property $ do
  program <- loadBreadboard
  forM_ ["rc", "div", "tri"] $ \circuit -> do
    let text = "comps " ++ circuit ++ " Cs, nets Cs Ns, best Cs Ns Wired P Cost?"
    old <- reference program text
    new <- native program text
    observations new === observations old
    answer <- one new
    groundAnswer answer
    wired <- binding "Wired" answer >>= list
    length wired === if circuit == "tri" then 1 else 0
    ps <- binding "P" answer >>= placed
    cost <- binding "Cost" answer >>= integer
    cost === scoreModel ps
    assert (validGrid wired 7 11 ps)

prop_native_report :: Property
prop_native_report = withTests 1 . property $ do
  program <- loadBreadboard
  old <- reference program "emit (report tri)?"
  new <- native program "emit (report tri)?"
  oldAnswer <- one old
  newAnswer <- one new
  let bytes = concatMap renderOutputEvent . answerOutput
  bytes newAnswer === bytes oldAnswer
  assert (not (null (bytes newAnswer)))
  -- Verify the report's constrained auxiliaries are ground independently of
  -- whether its formatter happened to accept them.
  optimum <- native program "comps tri Cs, nets Cs Ns, best Cs Ns Wired P Cost, score P Ground?"
  answer <- one optimum
  groundAnswer answer
  binding "Cost" answer >>= \cost -> binding "Ground" answer >>= (cost ===)

renderList :: [String] -> String
renderList values = "[" ++ intercalate ", " values ++ "]"

renderComponents :: [(Int, Int)] -> String
renderComponents nets = renderList
  [unwords ["c", "p" ++ show i, "r", "\"1k\"", "n" ++ show a, "n" ++ show b,
    show (i + 1), show (i + 1)] | (i, (a, b)) <- zip [0 :: Int ..] nets]

-- Enumerate coordinates directly, derive holes/nodes arithmetically, reject
-- shorts and overlapping holes, then score. No logic query is used here.
allGridPlacements :: [(Int, Int)] -> [Term] -> Integer -> Integer -> [[Placed]]
allGridPlacements nets wired lo hi = filter (validGrid wired lo hi) (sequence candidates)
  where
    candidates =
      [[Placed (Atom ("p" ++ show i)) (Atom ("n" ++ show a)) (Atom ("n" ++ show b))
          row col half (node * 10 + row) ((node + 1) * 10 + row) node (node + 1)
        | col <- [lo .. hi], half <- if i == 0 then [0] else [0, 1], let node = half * 100 + col]
        | (i, (a, b)) <- zip [0 :: Int ..] nets, let row = fromIntegral (i + 1)]

prop_generated_small_grids :: Property
prop_generated_small_grids = withTests 40 . property $ do
  -- Forty tests do not reach the full size of linear ranges. Keep all three
  -- component counts and all small columns/net IDs available from test one.
  nets <- forAll $ Gen.list (Range.constant 1 3) $
    (,) <$> Gen.int (Range.constant 0 3) <*> Gen.int (Range.constant 0 3)
  wiredIds <- forAll (Gen.subsequence [0 :: Int .. 3])
  width <- forAll (Gen.int (Range.constant 1 3))
  program <- loadBreadboard
  let wired = [Atom ("n" ++ show n) | n <- wiredIds]
      hi = fromIntegral (6 + width)
      arguments = renderComponents nets ++ " " ++ renderList ["n" ++ show n | n <- wiredIds] ++ " 7 " ++ show hi
      exhaustive = "solve " ++ arguments ++ " P, score P Cost?"
      optimum = "solve_min " ++ arguments ++ " P Cost?"
      physical = sort [(scoreModel ps, coordinates ps) | ps <- allGridPlacements nets wired 7 hi]
  oldAll <- reference program exhaustive
  newAll <- native program exhaustive
  observations newAll === observations oldAll
  oldBest <- reference program optimum
  newBest <- native program optimum
  observations newBest === observations oldBest
  actual <- mapM scored (summaryAnswers newAll)
  sort actual === physical
  classify "infeasible grid" (null physical)
  classify "jumpered net" (not (null wired))
  cover 10 "three components" (length nets == 3)
  case physical of
    [] -> summaryAnswers newBest === []
    _ -> do
      answer <- one newBest
      groundAnswer answer
      winner <- scored answer
      fst winner === minimum (map fst physical)
      assert (winner `elem` physical)
      ps <- binding "P" answer >>= placed
      assert (validGrid wired 7 hi ps)

prop_wide_disconnected :: Property
prop_wide_disconnected = withTests 1 . property $ do
  program <- loadBreadboard
  let nets = [(0, 1), (2, 3), (4, 5)]
      text = "solve_min " ++ renderComponents nets ++ " [] 1 16 P Cost?"
      physical = [(scoreModel ps, coordinates ps) | ps <- allGridPlacements nets [] 1 16]
  old <- reference program text
  new <- native program text
  observations new === observations old
  answer <- one new
  groundAnswer answer
  winner <- scored answer
  fst winner === minimum (map fst physical)
  assert (winner `elem` physical)
  ps <- binding "P" answer >>= placed
  assert (validGrid [] 1 16 ps)

machineBreadboardGroup :: Group
machineBreadboardGroup = Group "Machine CLP breadboard acceptance"
  [("shipped circuits match the reference optimum and physical grid", prop_shipped_circuits),
   ("native tri report is byte-identical and optimum is ground", prop_native_report),
   ("generated grids match exhaustive labeling and independent enumeration", prop_generated_small_grids),
   ("wide disconnected components match independent optimum", prop_wide_disconnected)]
