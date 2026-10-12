{-# LANGUAGE OverloadedStrings #-}

module MinesweeperTest (minesweeperGroup) where

import Control.Exception (evaluate)
import Data.List (intercalate, sort)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera
import System.Timeout (timeout)

data Window = Window Int Int Int deriving Show

renderRules :: [Window] -> String
renderRules rules = "[" ++ intercalate ", "
  ["window " ++ unwords (map show [w, h, cap]) | Window w h cap <- rules] ++ "]"

loadExample :: PropertyT IO Program
loadExample = evalIO (readFile "examples/minesweeper.nprolog") >>= evalEither . loadProgramText

solve :: Program -> String -> PropertyT IO QuerySummary
solve prog text = do
  annotate text
  query <- evalEither (parseQuery text)
  let result = solveAll prog query
  summaryErrors result === []
  summaryExhausted result === False
  pure result

asList :: Term -> PropertyT IO [Term]
asList term = case unfoldCons term of
  (values, Nothing) -> pure values
  _ -> annotateShow term >> failure

gridFrom :: Answer -> PropertyT IO [[Int]]
gridFrom answer = do
  term <- maybe (annotateShow answer >> failure) pure (lookup "Grid" (answerBindings answer))
  rows <- asList term
  mapM (\row -> asList row >>= mapM cell) rows
  where
    cell (IntLit 0) = pure 0
    cell (IntLit 1) = pure 1
    cell other = annotateShow other >> failure

validWindows :: [Window] -> [[Int]] -> Bool
validWindows rules grid = all valid rules
  where
    height = length grid
    width = case grid of row : _ -> length row; [] -> 0
    valid (Window w h cap) = and
      [sum [grid !! y !! x | y <- [top .. top + h - 1], x <- [left .. left + w - 1]] <= cap
      | top <- [0 .. height - h], left <- [0 .. width - w]]

chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks n xs = take n xs : chunks n (drop n xs)

prop_finite_model :: Property
prop_finite_model = withTests 100 $ property $ do
  width <- forAll (Gen.int (Range.linear 1 3))
  height <- forAll (Gen.int (Range.linear 1 3))
  bombs <- forAll (Gen.int (Range.linear 0 (width * height)))
  rules <- forAll $ Gen.list (Range.linear 0 3) $ do
    w <- Gen.int (Range.linear 1 4)
    h <- Gen.int (Range.linear 1 4)
    Window w h <$> Gen.int (Range.linear 0 (w * h))
  seed <- forAll (Gen.int (Range.linear (-1000) 1000))
  let expected = sort
        [grid | cells <- sequence (replicate (width * height) [0, 1]),
          sum cells == bombs, let grid = chunks width cells, validWindows rules grid]
      args = unwords (map show [width, height, bombs]) ++ " " ++ renderRules rules
  classify "impossible" (null expected)
  classify "odd boundary tiles" (odd width || odd height)
  classify "vacuous windows" (any (\(Window w h _) -> w > width || h > height) rules)
  prog <- loadExample
  -- Exact solution-set equality checks both soundness and completeness of
  -- overlapping windows, redundant tile counts and the seeded permutation.
  mapM_ (\text -> do
      result <- solve prog text
      actual <- mapM gridFrom (summaryAnswers result)
      sort actual === expected
    ) ["minefield " ++ args ++ " Grid?",
       "minefield_seed " ++ args ++ " " ++ show seed ++ " Grid?"]

prop_dense_acceptance :: Property
prop_dense_acceptance = withTests 1 $ property $ do
  prog <- loadExample
  let text seed = "once (minefield_seed 10 10 50 [window 2 2 2] " ++ show seed ++ " Grid)?"
  grids <- mapM (\seed -> do
      query <- evalEither (parseQuery (text seed))
      let result = solveAll prog query
      -- Force the full answer inside the deadline, not only a lazy wrapper.
      completed <- evalIO (timeout 15000000 (evaluate (length (show result))))
      case completed of Nothing -> annotate (text seed) >> failure; Just _ -> success
      summaryErrors result === []
      summaryExhausted result === False
      case summaryAnswers result of
        [answer] -> do
          grid <- gridFrom answer
          length grid === 10
          map length grid === replicate 10 10
          sum (concat grid) === 50
          assert (validWindows [Window 2 2 2] grid)
          pure grid
        other -> annotateShow other >> failure
    ) [42 :: Int, 43, 42]
  case grids of
    [first, second, repeated] -> do
      first === repeated
      first /== second
    _ -> failure
  rendered <- solve prog "show_seeded 10 10 50 [window 2 2 2] 42?"
  case summaryAnswers rendered of
    [answer] -> do
      let rows = lines (concatMap renderOutputEvent (answerOutput answer))
      length rows === 10
      length (filter (== '*') (concat rows)) === 50
    other -> annotateShow other >> failure

prop_boundaries_and_invalid_inputs :: Property
prop_boundaries_and_invalid_inputs = withTests 1 $ property $ do
  prog <- loadExample
  mapM_ (\text -> do
      result <- solve prog text
      summaryAnswers result === []
    ) ["mines 2 2 3 2 Grid?", "mines 0 2 0 2 Grid?", "mines 2 -1 0 2 Grid?",
       "mines 2 2 -1 2 Grid?", "mines 2 2 5 2 Grid?", "mines 2 2 0 -1 Grid?",
       "minefield 2 2 0 [window 0 2 2] Grid?", "mines 2.5 2 1 2 Grid?"]
  mapM_ (\(text, expected) -> do
      result <- solve prog text
      actual <- mapM gridFrom (summaryAnswers result)
      actual === [expected]
    ) [("mines 1 3 3 0 Grid?", [[1], [1], [1]]),
       ("mines 3 1 3 0 Grid?", [[1, 1, 1]]),
       ("mines 3 3 0 0 Grid?", replicate 3 (replicate 3 0)),
       ("minefield 3 3 9 [window 4 4 0] Grid?", replicate 3 (replicate 3 1))]
  -- A genuinely overlapping pair of rules, with a rectangular board.
  result <- solve prog "once (minefield_seed 8 6 12 [window 2 2 2, window 3 3 3] -42 Grid)?"
  case summaryAnswers result of
    [answer] -> do
      grid <- gridFrom answer
      map length grid === replicate 6 8
      sum (concat grid) === 12
      assert (validWindows [Window 2 2 2, Window 3 3 3] grid)
    other -> annotateShow other >> failure

minesweeperGroup :: Group
minesweeperGroup = Group "Minesweeper example"
  [("all small grids vs independent window model", prop_finite_model),
   ("50 bombs, 2x2 cap, seeded repeatability and rendering", prop_dense_acceptance),
   ("boundaries, impossible rules and combined windows", prop_boundaries_and_invalid_inputs)]
