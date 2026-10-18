{-# LANGUAGE OverloadedStrings #-}

-- Slot addresses may be recycled; the logical variables they represent may
-- not. Compare exact projected IDs and freshness in the ordered native
-- stream, rather than comparing rendered answers that rename free variables.
module CoreSlotsTest (coreSlotsGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import GHC.Float (castDoubleToWord64)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera hiding (Answer, solveQuery)
import qualified Infera.CLP as CLP
import qualified Infera.Core.Run as Run
import qualified Infera.Core.Store as Store
import qualified Infera.Engine.Reference as Reference

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

-- Bitwise floating point observations also distinguish negative zero, and
-- let a retained NaN compare equal to its own original snapshot.
bits :: Term -> Term
bits (FloatLit value) = Compound "$slot_float_bits"
  [IntLit (fromIntegral (castDoubleToWord64 value))]
bits (Compound name arguments) = Compound name (map bits arguments)
bits term = term

problemBits :: SolveError -> SolveError
problemBits problem = case problem of
  InstantiationError term -> InstantiationError (bits term)
  ExpectedInteger term -> ExpectedInteger (bits term)
  ExpectedNumber term -> ExpectedNumber (bits term)
  ModeError key index term -> ModeError key index (bits term)
  OutputModeError key index term -> OutputModeError key index (bits term)
  SortError key index sort' term -> SortError key index sort' (bits term)
  CLPTypeError term -> CLPTypeError (bits term)
  UnboundedDomain term -> UnboundedDomain (bits term)
  TypeError description term -> TypeError description (bits term)
  other -> other

data Observation
  = Answer [Term] Int [String] [OutputEvent]
  | Problem SolveError
  | Exhausted
  | Cut Int
  | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Search -> [Observation]
observe query = map item
  where
    item (Found state) =
      let substitution = CLP.stSubst (ssStore state)
          answer = Reference.projectAnswer query state
       in Answer
            [bits (deepWalk substitution (Var variable))
              | variable <- [0 .. queryNVars query - 1]]
            (ssFresh state) (Reference.answerResiduals answer) (ssOutput state)
    item (BranchError problem) = Problem (problemBits problem)
    item BranchExhausted = Exhausted
    item (CutMarker owner) = Cut owner
    item (ConsumedIncomplete key) = Incomplete (bits key)

drain :: IO Run.Step -> IO Search
drain action = do
  step <- action
  case step of
    Run.Stop -> pure []
    Run.Yield item next -> (item :) <$> drain next
    Run.Abandon reason -> fail ("native slot execution abandoned: " ++ reason)

native :: Int -> Program -> Query -> IO Search
native limit program query = do
  (reason, first) <- Run.runCoreWith limit program query
  case reason of
    Just unsupported -> fail ("native slot compilation rejected: " ++ unsupported)
    Nothing -> drain first

nativeStats :: Int -> Program -> Query -> IO (Search, (Int, Int, Int))
nativeStats limit program query = do
  (reason, first, statistics) <- Run.runCoreWithSlotStats limit program query
  case reason of
    Just unsupported -> fail ("native slot compilation rejected: " ++ unsupported)
    Nothing -> do
      items <- drain first
      counters <- statistics
      pure (items, counters)

limits :: [Int]
limits = [1, 16, Store.initialCollectLimit]

parity :: Program -> Query -> PropertyT IO Search
parity program query = do
  let expected = observe query (Reference.solveQuery program query)
  forM_ limits $ \limit -> do
    annotate ("collection limit " ++ show limit)
    items <- evalIO (native limit program query)
    observe query items === expected
  items <- evalIO (native Store.initialCollectLimit program query)
  pure items

loadFixture :: PropertyT IO (Program, [Query])
loadFixture = evalIO (loadFile "test/core/parity-slots.nprolog") >>= evalEither

prop_fixture :: Property
prop_fixture = unit $ do
  (program, queries) <- loadFixture
  assert (not (null queries))
  forM_ queries $ \query -> do
    annotate (show (queryGoals query))
    _ <- parity program query
    pure ()

recursiveSource :: String
recursiveSource = unlines
  [ "<- notable.",
    "spin 0.",
    "spin N <- N > 0, M is N - 1, spin M.",
    "app [] L L.",
    "app [H | T] L [H | R] <- app T L R.",
    "rev [] [].",
    "rev [H | T] R <- rev T RT, app RT [H] R."
  ]

prop_generated_reverse :: Property
prop_generated_reverse = withTests 100 . property $ do
  fields <- forAll (Gen.list (Range.linear 0 18)
    (Gen.choice [Var <$> Gen.int (Range.linear 0 3), IntLit <$> Gen.integral (Range.linear (-3) 3)]))
  depth <- forAll (Gen.int (Range.linear 0 30))
  let input = mkList fields Nothing
      query = Query
        [Compound "rev" [input, Var 4], Compound "spin" [IntLit (toInteger depth)]]
        [("V0", 0), ("V1", 1), ("V2", 2), ("V3", 3), ("Out", 4)] 5
  program <- evalEither (loadProgramText recursiveSource)
  items <- parity program query
  [deepWalk (CLP.stSubst (ssStore state)) (Var 4) | Found state <- items]
    === [mkList (reverse fields) Nothing]

prop_generated_escaping_slots :: Property
prop_generated_escaping_slots = withTests 100 . property $ do
  width <- forAll (Gen.int (Range.linear 1 16))
  shared <- forAll (Gen.int (Range.linear 0 (width - 1)))
  depth <- forAll (Gen.int (Range.linear 1 40))
  let names = ["X" ++ show index | index <- [0 .. width - 1]]
      fields = names ++ [names !! shared, names !! shared]
      source = recursiveSource ++ unlines
        ["escape N Out <- Out = (wide " ++ unwords fields ++ "), spin N."]
  program <- evalEither (loadProgramText source)
  query <- evalEither (parseQuery ("escape " ++ show depth ++ " Out?"))
  items <- parity program query
  case [deepWalk (CLP.stSubst (ssStore state)) (Var 0) | Found state <- items] of
    [Compound "wide" values] -> do
      length values === width + 2
      take width values === [Var variable | Var variable <- take width values]
      values !! width === values !! shared
      values !! (width + 1) === values !! shared
      assert (and [left /= right | (i, left) <- zip [0 :: Int ..] (take width values),
        (j, right) <- zip [0 :: Int ..] (take width values), i < j])
    other -> annotateShow other >> failure

prop_generated_mutual_tail :: Property
prop_generated_mutual_tail = withTests 100 . property $ do
  depth <- forAll (Gen.int (Range.linear 1 50))
  width <- forAll (Gen.int (Range.linear 0 14))
  initial <- forAll (Gen.integral (Range.linear (-10) 10))
  let extras = ["Unused" ++ show index ++ " = kept" | index <- [0 .. width - 1]]
      source = unlines
        [ "<- notable.",
          "narrow 0 Acc Acc.",
          "narrow N Acc Out <- N > 0, Next is Acc + N, M is N - 1, wide M Next Out.",
          "wide 0 Acc Acc.",
          "wide N Acc Out <- " ++ concatMap (++ ", ") extras ++
            "N > 0, M is N - 1, Next is Acc + N, Alias = Next, narrow M Alias Out."
        ]
  program <- evalEither (loadProgramText source)
  query <- evalEither (parseQuery ("narrow " ++ show depth ++ " (" ++ show initial ++ ") Out?"))
  items <- parity program query
  [answerBindings (Reference.projectAnswer query state) | Found state <- items]
    === [[("Out", IntLit (initial + toInteger (depth * (depth + 1) `div` 2)))]]

prop_reused_ground_loop :: Property
prop_reused_ground_loop = unit $ do
  (program, _) <- loadFixture
  query <- evalEither (parseQuery "count 4000 0 Result?")
  (items, (allocated, reused, cells)) <- evalIO (nativeStats Store.initialCollectLimit program query)
  [answerBindings (Reference.projectAnswer query state) | Found state <- items]
    === [[("Result", IntLit 8002000)]]
  annotateShow (allocated, reused, cells)
  -- A facade replay or a metric increment without actual frame reuse cannot
  -- satisfy both the high reuse count and the low fresh-frame count.
  assert (reused > 3000)
  assert (allocated < 100)
  assert (cells >= reused)

prop_reused_reverse :: Property
prop_reused_reverse = unit $ do
  program <- evalEither (loadProgramText recursiveSource)
  let fields = map IntLit [1 .. 12]
      query = Query [Compound "rev" [mkList fields Nothing, Var 0]] [("Out", 0)] 1
  (items, (allocated, reused, cells)) <- evalIO (nativeStats Store.initialCollectLimit program query)
  [deepWalk (CLP.stSubst (ssStore state)) (Var 0) | Found state <- items]
    === [mkList (reverse fields) Nothing]
  annotateShow (allocated, reused, cells)
  assert (allocated > 0)
  assert (reused > 0)
  assert (cells >= reused)

prop_saved_frame_alternative :: Property
prop_saved_frame_alternative = unit $ do
  program <- evalEither (loadProgramText (unlines
    [ "<- notable.",
      "offer Out <- (Out = left ; Out = right), sink Out.",
      "sink X."
    ]))
  query <- evalEither (parseQuery "offer Out?")
  (reason, first, statistics) <- evalIO (Run.runCoreWithSlotStats Store.initialCollectLimit program query)
  reason === Nothing
  step <- evalIO first
  case step of
    Run.Yield item next -> do
      -- The pending right alternative captures offer's activation. Its
      -- first tail call must allocate a separate sink frame, even though
      -- the selected left value is ground and the current body is done.
      (allocated, reused, cells) <- evalIO statistics
      annotateShow (allocated, reused, cells)
      assert (allocated > 0)
      reused === 0
      cells === 0
      observe query [item] === take 1 (observe query (Reference.solveQuery program query))
      remaining <- evalIO (drain next)
      observe query (item : remaining) === observe query (Reference.solveQuery program query)
    _ -> annotate "saved-frame alternative produced no first answer" >> failure

prop_retained_interleaved_answers :: Property
prop_retained_interleaved_answers = unit $ do
  (program, _) <- loadFixture
  query <- evalEither (parseQuery "branch 30 Out?")
  other <- evalEither (parseQuery "constraint_box 30 Out, Out = (box X), label [X]?")
  (reason, first) <- evalIO (Run.runCoreWith 1 program query)
  reason === Nothing
  step <- evalIO first
  case step of
    Run.Yield item next -> do
      let saved = observe query [item]
      forced <- evalIO (evaluate (length (show saved)))
      assert (forced > 0)
      otherItems <- evalIO (native 1 program other)
      observe other otherItems === observe other (Reference.solveQuery program other)
      remaining <- evalIO (drain next)
      observe query (item : remaining) === observe query (Reference.solveQuery program query)
      observe query [item] === saved
    _ -> annotate "retained-answer query produced no native first answer" >> failure

prop_fresh_ids_after_zero_var_and_retries :: Property
prop_fresh_ids_after_zero_var_and_retries = unit $ do
  let source = recursiveSource ++ unlines
        [ "pause.",
          "open N Out <- Out = (pair X Y), spin N.",
          "reject (pair X X) <- spin 3."
        ]
  program <- evalEither (loadProgramText source)
  forM_
    [ "pause, spin 20, pause, open 20 Out?",
      "open 20 First, pause, open 20 Second?",
      "(reject (pair a b), open 20 Out ; pause, open 20 Out)?",
      "minimize Cost (Cost = 1, pause, open 20 Before), pause, open 20 After?",
      "findall X (pause, open 20 X) Values, pause, open 20 After?"
    ] $ \text -> do
      query <- evalEither (parseQuery text)
      _ <- parity program query
      pure ()

prop_scalar_slots :: Property
prop_scalar_slots = unit $ do
  let source = recursiveSource ++ "keep N X Out <- Out = (pair X Y), spin N.\n"
      values = [IntLit (2 ^ (90 :: Int) + 9), FloatLit (-0.0), FloatLit (0 / 0),
        FloatLit (1 / 0), CharLit '\955', StrLit "kept\0\955", Atom "kept"]
  program <- evalEither (loadProgramText source)
  forM_ values $ \value -> do
    let query = Query [Compound "keep" [IntLit 30, value, Var 0]] [("Out", 0)] 1
    _ <- parity program query
    pure ()

coreSlotsGroup :: Group
coreSlotsGroup = Group "core reusable variable slots and tail frames"
  [ ("fixture", prop_fixture),
    ("generated_reverse", prop_generated_reverse),
    ("generated_escaping_slots", prop_generated_escaping_slots),
    ("generated_mutual_tail", prop_generated_mutual_tail),
    ("reused_ground_loop", prop_reused_ground_loop),
    ("reused_reverse", prop_reused_reverse),
    ("saved_frame_alternative", prop_saved_frame_alternative),
    ("retained_interleaved_answers", prop_retained_interleaved_answers),
    ("fresh_ids_after_zero_var_and_retries", prop_fresh_ids_after_zero_var_and_retries),
    ("scalar_slots", prop_scalar_slots)
  ]
