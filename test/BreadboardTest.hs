{-# LANGUAGE OverloadedStrings #-}

module BreadboardTest (breadboardGroup) where

import Control.Exception (evaluate)
import Data.List (intercalate, nub)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera
import System.Timeout (timeout)

loadExample :: PropertyT IO Program
loadExample = do
  source <- evalIO (readFile "examples/breadboard.nprolog")
  items <- evalEither (parseFile source)
  -- The shipped file includes report queries for interactive use. Build and
  -- check its declarations/clauses without executing those entry points.
  evalEither (buildChecked [item | item <- items, case item of TLQuery _ -> False; _ -> True])

solve :: Program -> String -> PropertyT IO QuerySummary
solve prog text = do
  annotate text
  query <- evalEither (parseQuery text)
  let result = solveAll prog query
  completed <- evalIO (timeout 15000000 (evaluate (length (show result))))
  case completed of
    Nothing -> annotate "Breadboard query exceeded 15 seconds" >> failure
    Just _ -> success
  summaryErrors result === []
  summaryExhausted result === False
  pure result

binding :: String -> Answer -> PropertyT IO Term
binding name answer = maybe (annotateShow answer >> failure) pure (lookup name (answerBindings answer))

integer :: Term -> PropertyT IO Integer
integer (IntLit n) = pure n
integer other = annotateShow other >> failure

asList :: Term -> PropertyT IO [Term]
asList term = case unfoldCons term of
  (values, Nothing) -> pure values
  _ -> annotateShow term >> failure

-- This arithmetic model does not use CLP, the Infera score predicate, or the
-- placement model's stored node/hole fields.
data Placed = Placed Term Term Integer Integer Integer deriving Show

placement :: Term -> PropertyT IO [Placed]
placement term = asList term >>= mapM part
  where
    part (Compound "pl" [_, _, _, a, b, _, IntLit row, IntLit col, IntLit half, _, _, _, _]) =
      pure (Placed a b row col half)
    part other = annotateShow other >> failure

referenceScore :: [Placed] -> Integer
referenceScore parts = sum [abs (col - 9) | Placed _ _ _ col _ <- parts] +
  sum [pair p q | (i, p) <- zip [0 :: Int ..] parts, q <- drop (i + 1) parts]
  where
    pair (Placed a b _ col half) (Placed c d _ col' half') =
      (if half == half' then 0 else 2) +
      (if half == half' && abs (col - col') <= 2 && not (a == c || a == d || b == c || b == d)
        then 4 else 0)

validPlacement :: [Term] -> Integer -> Integer -> [Placed] -> Bool
validPlacement wired lo hi parts = not (null parts) && firstOnTop &&
  all inBounds parts && length holes == length (nub holes) &&
  and [compatible p q | (i, p) <- zip [0 :: Int ..] pins, q <- drop (i + 1) pins]
  where
    firstOnTop = case parts of Placed _ _ _ _ h : _ -> h == 0; [] -> False
    inBounds (Placed _ _ row col half) = row >= 1 && row <= 5 && col >= lo && col <= hi && half `elem` [0, 1]
    holes = concat [[(half * 100 + col) * 10 + row, (half * 100 + col + 1) * 10 + row]
      | Placed _ _ row col half <- parts]
    pins = concat [[(a, half * 100 + col), (b, half * 100 + col + 1)]
      | Placed a b _ col half <- parts]
    compatible (a, node) (b, node')
      | a == b = a `elem` wired || node == node'
      | otherwise = node /= node'

renderList :: [String] -> String
renderList xs = "[" ++ intercalate ", " xs ++ "]"

renderPlaced :: Int -> (Int, Int, Int, Int) -> String
renderPlaced i (a, b, col, half) = unwords
  ["pl", "p" ++ show i, "r", "\"1k\"", "n" ++ show a, "n" ++ show b,
   show (i + 1), show row, show col, show half, show (node * 10 + row),
   show ((node + 1) * 10 + row), show node, show (node + 1)]
  where
    row = i `mod` 5 + 1
    node = half * 100 + col

prop_score_model :: Property
prop_score_model = withTests 100 $ property $ do
  parts <- forAll $ Gen.list (Range.linear 0 5) $ (,,,)
    <$> Gen.int (Range.linear 0 3) <*> Gen.int (Range.linear 0 3)
    <*> Gen.int (Range.linear 1 16) <*> Gen.int (Range.linear 0 1)
  let text = renderList (zipWith renderPlaced [0 ..] parts)
  prog <- loadExample
  result <- solve prog ("P = " ++ text ++ ", score P Ground, score_constraints P Cost?")
  case summaryAnswers result of
    [answer] -> do
      cost <- binding "Cost" answer >>= integer
      ground <- binding "Ground" answer >>= integer
      ps <- binding "P" answer >>= placement
      cost === ground
      cost === referenceScore ps
    other -> annotateShow other >> failure

prop_bounded_optimum :: Property
prop_bounded_optimum = withTests 75 $ property $ do
  nets <- forAll $ Gen.list (Range.linear 1 3) $
    (,) <$> Gen.int (Range.linear 0 3) <*> Gen.int (Range.linear 0 3)
  wired <- forAll $ Gen.subsequence [0 :: Int .. 3]
  width <- forAll (Gen.int (Range.linear 1 3))
  let cs = renderList [unwords ["c", "p" ++ show i, "r", "\"1k\"", "n" ++ show a,
              "n" ++ show b, show (i + 1), show (i + 1)]
            | (i, (a, b)) <- zip [0 :: Int ..] nets]
      ws = renderList ["n" ++ show n | n <- wired]
      args = cs ++ " " ++ ws ++ " 7 " ++ show (6 + width)
  prog <- loadExample
  -- Exhaustive ordinary labeling and the original ground score provide the
  -- entire reference set. The optimum must belong to that set, including ties.
  reference <- solve prog ("solve " ++ args ++ " P, score P Cost?")
  scored <- mapM (\answer -> do
      cost <- binding "Cost" answer >>= integer
      p <- binding "P" answer
      pure (cost, p)) (summaryAnswers reference)
  optimized <- solve prog ("solve_min " ++ args ++ " P Cost?")
  classify "impossible placement" (null scored)
  classify "jumpered nets" (not (null wired))
  case scored of
    [] -> summaryAnswers optimized === []
    _ -> case summaryAnswers optimized of
      [answer] -> do
        cost <- binding "Cost" answer >>= integer
        p <- binding "P" answer
        cost === minimum (map fst scored)
        assert ((cost, p) `elem` scored)
        ps <- placement p
        cost === referenceScore ps
        assert (validPlacement [Atom ("n" ++ show n) | n <- wired] 7 (fromIntegral (6 + width)) ps)
      other -> annotateShow other >> failure

prop_score_auxiliary_groundness :: Property
prop_score_auxiliary_groundness = withTests 1 $ property $ do
  prog <- loadExample
  -- Enumerate only placement variables, as solve_min does. Every auxiliary
  -- Boolean, absolute distance and sum must determine the ground cost at a
  -- leaf, including non-winning leaves and both sides of the cramped cutoff.
  mapM_ (\net -> do
      result <- solve prog ("[X,Y] in 7..11, [H,J] in 0..1, P = " ++
        "[pl p r \"1k\" a b 1 1 X H 0 0 0 0, " ++
        "pl q r \"1k\" " ++ net ++ " d 2 2 Y J 0 0 0 0], " ++
        "score_constraints P Cost, label [X,Y,H,J]?")
      length (summaryAnswers result) === 100
      mapM_ (\answer -> do
          ps <- binding "P" answer >>= placement
          cost <- binding "Cost" answer >>= integer
          cost === referenceScore ps
        ) (summaryAnswers result)
    ) ["a", "c"]

prop_standard_acceptance :: Property
prop_standard_acceptance = withTests 1 $ property $ do
  prog <- loadExample
  mapM_ (\circuit -> do
      let prefix = "comps " ++ circuit ++ " Cs, nets Cs Ns, "
          exhaustive = "once (multi_nets Cs Ns MNs, length MNs M, between 0 M K, " ++
            "choose K MNs Wired, windows Ws, member (win Lo Hi) Ws, " ++
            "minimize Cost (solve Cs Wired Lo Hi P, score P Cost))?"
      reference <- solve prog (prefix ++ exhaustive)
      optimized <- solve prog (prefix ++ "best Cs Ns Wired P Cost?")
      case (summaryAnswers reference, summaryAnswers optimized) of
        ([old], [new]) -> do
          oldCost <- binding "Cost" old >>= integer
          newCost <- binding "Cost" new >>= integer
          newCost === oldCost
          oldWired <- binding "Wired" old >>= asList
          newWired <- binding "Wired" new >>= asList
          newWired === oldWired
          length newWired === if circuit == "tri" then 1 else 0
          ps <- binding "P" new >>= placement
          newCost === referenceScore ps
          assert (validPlacement newWired 7 11 ps)
        other -> annotateShow other >> failure
    ) ["rc", "div", "tri"]
  -- Exercise the shipped reporting path, which must observe a ground optimum.
  rendered <- solve prog "emit (report tri)?"
  case summaryAnswers rendered of
    [answer] -> assert (not (null (answerOutput answer)))
    other -> annotateShow other >> failure

data FlexPlaced = FlexPlaced Term Term Term Integer Integer Integer Integer Integer Integer Integer
  deriving (Eq, Show)

data Jumper = Jumper Term Integer Integer Integer Integer Integer Integer
  deriving (Eq, Show)

flexPlacement :: Term -> PropertyT IO [FlexPlaced]
flexPlacement term = asList term >>= mapM part
  where
    part (Compound "pl" [_, kind, _, a, b, _, IntLit row, IntLit col, IntLit half,
                         IntLit ha, IntLit hb, IntLit na, IntLit nb]) =
      pure (FlexPlaced kind a b row col half ha hb na nb)
    part other = annotateShow other >> failure

flexJumpers :: Term -> PropertyT IO [Jumper]
flexJumpers term = asList term >>= mapM item
  where
    item (Compound "jmp" [net, IntLit ra, IntLit rb, IntLit ha, IntLit hb, IntLit na, IntLit nb]) =
      pure (Jumper net ra rb ha hb na nb)
    item other = annotateShow other >> failure

validFlexPlacement :: Integer -> Integer -> [FlexPlaced] -> [Jumper] -> Bool
validFlexPlacement lo hi parts jumpers =
  not (null parts) && firstOnTop &&
  all validPart parts && all validJumper jumpers &&
  length allHoles == length (nub allHoles) &&
  and [na /= nb | (a, na) <- pins, (b, nb) <- pins, a /= b] &&
  all netConnected netNames
  where
    polarizedKinds = [Atom "d", Atom "led", Atom "ecap"]
    firstOnTop = case parts of FlexPlaced _ _ _ _ _ h _ _ _ _ : _ -> h == 0; [] -> False
    validPart (FlexPlaced kind _ _ row col half ha hb na nb) =
      let base = half * 100 + col
          orientationOk
            | kind `elem` polarizedKinds = na == base && nb == base + 1
            | otherwise = (na == base && nb == base + 1) || (na == base + 1 && nb == base)
       in row >= 1 && row <= 5 && col >= lo && col <= hi && half `elem` [0, 1] &&
          orientationOk && ha == na * 10 + row && hb == nb * 10 + row
    validJumper (Jumper net ra rb ha hb na nb) =
      ra >= 1 && ra <= 5 && rb >= 1 && rb <= 5 &&
      na /= nb && ha == na * 10 + ra && hb == nb * 10 + rb &&
      (net, na) `elem` pins && (net, nb) `elem` pins
    compHoles = concat [[ha, hb] | FlexPlaced _ _ _ _ _ _ ha hb _ _ <- parts]
    jmpHoles = concat [[ha, hb] | Jumper _ _ _ ha hb _ _ <- jumpers]
    allHoles = compHoles ++ jmpHoles
    pins = concat [[(a, na), (b, nb)] | FlexPlaced _ a b _ _ _ _ _ na nb <- parts]
    netNames = nub (map fst pins)
    netConnected net =
      let nodes = nub [n | (m, n) <- pins, m == net]
          edges = [(na, nb) | Jumper m _ _ _ _ na nb <- jumpers, m == net]
       in length nodes == 1 + length edges

prop_flexible_placement :: Property
prop_flexible_placement = withTests 1 $ property $ do
  prog <- loadExample
  -- Reversed parallel resistors need 1 jumper without flipping, 0 with flipping.
  unflippedPar <- solve prog "comps par_flip Cs, nets Cs Ns, best Cs Ns Wired P Cost?"
  case summaryAnswers unflippedPar of
    [ans] -> (binding "Wired" ans >>= asList >>= \w -> length w === 1)
    other -> annotateShow other >> failure
  mapM_ (\(circuit, expectedJumpers) -> do
      result <- solve prog ("comps " ++ circuit ++ " Cs, nets Cs Ns, best_flex Cs Ns JumpNets P Jumpers Cost?")
      case summaryAnswers result of
        [ans] -> do
          jumpNets <- binding "JumpNets" ans >>= asList
          fps <- binding "P" ans >>= flexPlacement
          ps <- binding "P" ans >>= placement
          js <- binding "Jumpers" ans >>= flexJumpers
          cost <- binding "Cost" ans >>= integer
          length jumpNets === expectedJumpers
          length js === expectedJumpers
          cost === referenceScore ps
          assert (validFlexPlacement 7 11 fps js)
        other -> annotateShow other >> failure
    ) [("par_flip" :: String, 0 :: Int), ("par_diode", 0), ("anti_diode", 1), ("ladder6", 0), ("tri", 1)]
  rendered <- solve prog "emit (report_flex anti_diode), emit (report_flex ladder6)?"
  case summaryAnswers rendered of
    [ans] -> assert (not (null (answerOutput ans)))
    other -> annotateShow other >> failure

breadboardGroup :: Group
breadboardGroup = Group "Breadboard branch-and-bound"
  [("constrained score vs independent arithmetic", prop_score_model),
   ("bounded optima vs exhaustive placements", prop_bounded_optimum),
   ("score auxiliaries ground after placement-only labeling", prop_score_auxiliary_groundness),
   ("standard circuits and report acceptance", prop_standard_acceptance),
   ("flexible placement with flipping, CLP rows and jumper holes", prop_flexible_placement)]

