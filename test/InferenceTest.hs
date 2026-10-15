{-# LANGUAGE OverloadedStrings #-}

-- Inference is permitted to remove choice points, never observable results.
-- The reference below changes only the inferred pruning fields of an already
-- inferred Program: declared contracts, indexes, graph facts and tabling stay
-- identical. Structural generators retain Hedgehog's ordinary shrinking.
module InferenceTest (inferenceGroup) where

import qualified Data.Map.Strict as Map
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

generated :: TestLimit -> PropertyT IO () -> Property
generated n = withTests n . property

withoutInferredPruning :: Program -> Program
withoutInferredPruning program = program
  { progPreds = Map.map disable (progPreds program) }
  where
    disable predicate = predicate
      { predInferred = (predInferred predicate) { sigDet = Nondet, sigSwitch = [] } }

-- Internal fresh-variable ids are implementation details. Projected answer
-- rendering already names them by occurrence; errors need the same treatment.
normalizeError :: SolveError -> SolveError
normalizeError err = case err of
  InstantiationError t -> InstantiationError (canonical t)
  ExpectedInteger t -> ExpectedInteger (canonical t)
  ExpectedNumber t -> ExpectedNumber (canonical t)
  ModeError k i t -> ModeError k i (canonical t)
  OutputModeError k i t -> OutputModeError k i (canonical t)
  SortError k i s t -> SortError k i s (canonical t)
  CLPTypeError t -> CLPTypeError (canonical t)
  UnboundedDomain t -> UnboundedDomain (canonical t)
  TypeError description t -> TypeError description (canonical t)
  _ -> err
  where
    canonical = fst . canonicalize emptySubst

type Observation = ([(String, [OutputEvent])], [SolveError], Bool)

observe :: QuerySummary -> Observation
observe summary =
  ( [(showAnswer answer, answerOutput answer) | answer <- summaryAnswers summary],
    map normalizeError (summaryErrors summary),
    summaryExhausted summary
  )

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (loadProgramText source)

query :: String -> PropertyT IO Query
query text = annotate text >> evalEither (parseQuery text)

-- Ordered answers include multiplicity, residual constraints and output. A
-- sorted set comparison would miss lost duplicate answers and changed cuts.
equivalent :: Program -> String -> PropertyT IO QuerySummary
equivalent program text = do
  q <- query text
  let inferred = solveAll program q
      reference = solveAll (withoutInferredPruning program) q
  observe inferred === observe reference
  pure inferred

expectAnswers :: QuerySummary -> [String] -> PropertyT IO ()
expectAnswers summary answers = do
  map showAnswer (summaryAnswers summary) === answers
  summaryErrors summary === []
  summaryExhausted summary === False

signature :: Program -> PredKey -> PropertyT IO Signature
signature program key = case lookupPred key program of
  Nothing -> annotateShow key >> failure
  Just predicate -> pure (predInferred predicate)

-- These expected answers are independent of either execution path. In
-- particular, making all inference nondet cannot make the positive test pass.
prop_alternative_modes_regression :: Property
prop_alternative_modes_regression = unit $ do
  program <- load $ unlines
    [ "relation : semidet (int: <=) (int: =>).",
      "relation : nondet (int: =>) (int: <=).",
      "relation 1 0.",
      "relation 2 0.",
      "wrapper X <- relation X 0."
    ]
  direct <- equivalent program "relation X 0?"
  expectAnswers direct ["X = 1", "X = 2"]
  wrapped <- equivalent program "wrapper X?"
  expectAnswers wrapped ["X = 1", "X = 2"]

helperChain :: Int -> String -> String
helperChain depth terminal = unlines
  (["helper" ++ show i ++ " X <- helper" ++ show (i + 1) ++ " X." | i <- [0 .. depth - 1]]
   ++ ["helper" ++ show depth ++ " X" ++ terminal])

freeChainProgram :: Int -> String
freeChainProgram depth = helperChain depth "." ++ unlines
  [ "select 0 first.",
    "select N second <- N != 0.",
    "wrapper R <- helper0 N, select N R."
  ]

prop_groundness_chain_regression :: Property
prop_groundness_chain_regression = unit $ do
  program <- load (freeChainProgram 16)
  answer <- equivalent program "wrapper R?"
  expectAnswers answer ["R = first", "R = second"]
  sig <- signature program ("helper0", 1)
  map argMode (sigArgs sig) === [ModeInOut]
  inputs <- load $ unlines
    (["input" ++ show i ++ " X Y <- input" ++ show (i + 1) ++ " X Y." | i <- [0 :: Int .. 15]]
     ++ ["input16 X Y <- Y is X + 1."])
  inputSig <- signature inputs ("input0", 2)
  map argMode (sigArgs inputSig) === [ModeIn, ModeOut]
  value <- equivalent inputs "input0 2 Y?"
  expectAnswers value ["Y = 3"]

prop_mixed_numeric_term_regression :: Property
prop_mixed_numeric_term_regression = unit $ do
  program <- load "p 1 first.\np X second <- X != 1.0."
  answer <- equivalent program "p 1 R?"
  expectAnswers answer ["R = first", "R = second"]
  mixedGuards <- load "p X first <- X >= 1.0.\np X second <- X != 1.0."
  guarded <- equivalent mixedGuards "p 1 R?"
  expectAnswers guarded ["R = first", "R = second"]
  -- A variable or partially instantiated head is not a distinct literal.
  generic <- load "p X first.\np X second <- X == 1."
  genericResult <- equivalent generic "p 1 R?"
  expectAnswers genericResult ["R = first", "R = second"]
  partial <- load "p (box X) first.\np X second <- X != 1."
  partialResult <- equivalent partial "p (box 1) R?"
  expectAnswers partialResult ["R = first", "R = second"]

prop_lexical_guards_regression :: Property
prop_lexical_guards_regression = unit $
  mapM_ checkLexical [(Atom "b", Atom "a"), (StrLit "b", StrLit "a"), (CharLit 'b', CharLit 'a')]
  where
    checkLexical (high, low) = do
      let source = "p " ++ show high ++ " first.\np X second <- X > " ++ show low ++ "."
      program <- load source
      answer <- equivalent program ("p " ++ show high ++ " R?")
      expectAnswers answer ["R = first", "R = second"]

prop_call_alias_regressions :: Property
prop_call_alias_regressions = unit $
  mapM_ checkAliased
    [ "p X 1 <- X > 0.\np X -1 <- X <= 0.",
      "p 1 1.\np X -1 <- X <= 0."
    ]
  where
    checkAliased source = do
      program <- load source
      result <- equivalent program "p U U?"
      expectAnswers result ["U = 1", "U = -1"]

prop_open_label_groundness_regressions :: Property
prop_open_label_groundness_regressions = unit $
  mapM_ checkOpenLabel ["X", "[1 | X]"]
  where
    checkOpenLabel argument = do
      program <- load $ unlines
        [ "choose 1 a.",
          "choose 2 b.",
          "p X Y <- label " ++ argument ++ ", choose X Y."
        ]
      result <- equivalent program "p X Y?"
      expectAnswers result ["X = 1, Y = a", "X = 2, Y = b"]

prop_nan_swapped_guards_regression :: Property
prop_nan_swapped_guards_regression = unit $ do
  program <- load $ unlines
    [ "p X first <- X > 0.",
      "p X second <- 0 > X.",
      "wrapper R <- N is (-1.0) ^ 0.5, p N R."
    ]
  result <- equivalent program "wrapper R?"
  -- Numeric ordering places NaN above non-NaNs. Reversing operands must
  -- reverse the ordering; Double's default Ord instance violates this.
  expectAnswers result ["R = first"]

prop_numeric_order_laws :: Property
prop_numeric_order_laws = generated 100 $ do
  let numbers = Gen.choice
        [ NVInt <$> Gen.integral (Range.linear (-5) 5),
          NVFloat <$> Gen.element [0 / 0, 1 / 0, -1 / 0, -2, -1, 0, 1, 2]
        ]
      reverseOrder LT = GT
      reverseOrder GT = LT
      reverseOrder EQ = EQ
  a <- forAll numbers
  b <- forAll numbers
  compareNumeric a a === EQ
  compareNumeric a b === reverseOrder (compareNumeric b a)

prop_arithmetic_input_regression :: Property
prop_arithmetic_input_regression = unit $ do
  program <- load "c X Y <- X #< 10, Y is X + 1."
  sig <- signature program ("c", 2)
  map argMode (sigArgs sig) === [ModeIn, ModeOut]
  result <- equivalent program "c 2 Y?"
  expectAnswers result ["Y = 3"]
  invalid <- equivalent program "c X Y?"
  assert (not (null (summaryErrors invalid)))

prop_positive_optimizations :: Property
prop_positive_optimizations = unit $ do
  program <- load $ unlines
    [ "flag 0 zero.",
      "flag N nonzero <- N != 0.",
      "append [] R R.",
      "append [H | T] R [H | Rest] <- append T R Rest."
    ]
  flag <- signature program ("flag", 2)
  sigDet flag === Semidet
  sigSwitch flag === [0]
  append <- signature program ("append", 3)
  sigDet append === Semidet
  sigSwitch append === [0]
  result <- equivalent program "append [a, b] [c] R?"
  expectAnswers result ["R = [a, b, c]"]
  open <- equivalent program "flag N R?"
  expectAnswers open ["N = 0, R = zero", "R = nonzero, N != 0"]

-- Literal kinds remain explicit so a mixed integer/float case shrinks to a
-- small cross-sort counterexample instead of disappearing into arbitrary text.
genLiteral :: Gen Term
genLiteral = Gen.choice
  [ IntLit <$> Gen.integral (Range.linear (-2) 2),
    FloatLit . fromIntegral <$> (Gen.integral (Range.linear (-2) 2) :: Gen Integer),
    Atom <$> Gen.element ["a", "b", "c"],
    StrLit <$> Gen.element ["a", "b", "c"],
    CharLit <$> Gen.element ['a', 'b', 'c']
  ]

genOperator :: Gen String
genOperator = Gen.element ["==", "!=", "<", "<=", ">", ">="]

prop_generated_literal_guards :: Property
prop_generated_literal_guards = generated 500 $ do
  headLiteral <- forAll (Gen.maybe genLiteral)
  guardLiteral <- forAll genLiteral
  actual <- forAll genLiteral
  operator <- forAll genOperator
  open <- forAll Gen.bool
  reverseGuard <- forAll Gen.bool
  noIndex <- forAll Gen.bool
  let guard = if reverseGuard
        then "(" ++ show guardLiteral ++ ") " ++ operator ++ " X"
        else "X " ++ operator ++ " (" ++ show guardLiteral ++ ")"
      source = unlines
        [ if noIndex then "<- noindex." else "<- index.",
          "p " ++ maybe "X" show headLiteral ++ " first.",
          "p X second <- " ++ guard ++ "."
        ]
  classify "free query with residuals" open
  classify "term equality/disequality" (operator `elem` ["==", "!="])
  classify "numeric comparison" (operator `elem` ["<", "<=", ">", ">="])
  program <- load source
  _ <- equivalent program ("p " ++ (if open then "X" else show actual) ++ " R?")
  pure ()

data HeadShape = PlainHead | NestedHead | AliasedHead | NestedAliasedHead
  deriving (Eq, Show)

prop_generated_head_paths :: Property
prop_generated_head_paths = generated 500 $ do
  shape <- forAll (Gen.element [PlainHead, NestedHead, AliasedHead, NestedAliasedHead])
  operator1 <- forAll genOperator
  operator2 <- forAll genOperator
  a <- forAll genLiteral
  b <- forAll genLiteral
  free <- forAll Gen.bool
  swapped <- forAll Gen.bool
  let (head1, head2, actual) = case shape of
        PlainHead -> ("X Y", "X Y", (if free then "A" else show a) ++ " " ++ show b)
        NestedHead -> ("(box X) Y", "(box X) Y", "(box " ++ (if free then "A" else show a) ++ ") " ++ show b)
        AliasedHead -> ("X X Y", "X Y Y", (if free then "A" else show a) ++ " " ++ show a ++ " " ++ show b)
        NestedAliasedHead -> ("(box X) X Y", "(box X) Y X", "(box " ++ (if free then "A" else show a) ++ ") " ++ show a ++ " " ++ show b)
      guard2 = if swapped then "Y " ++ operator2 ++ " X" else "X " ++ operator2 ++ " Y"
      source = unlines
        [ "p " ++ head1 ++ " first <- X " ++ operator1 ++ " Y.",
          "p " ++ head2 ++ " second <- " ++ guard2 ++ "."
        ]
  classify "nested head paths" (shape `elem` [NestedHead, NestedAliasedHead])
  classify "aliased head paths" (shape `elem` [AliasedHead, NestedAliasedHead])
  classify "partially instantiated head" free
  program <- load source
  _ <- equivalent program ("p " ++ actual ++ " R?")
  pure ()

prop_generated_declared_modes :: Property
prop_generated_declared_modes = generated 300 $ do
  low <- forAll (Gen.integral (Range.linear (-5) 5) :: Gen Integer)
  key <- forAll (Gen.integral (Range.linear (-5) 5) :: Gen Integer)
  depth <- forAll (Gen.int (Range.linear 0 5))
  firstDet <- forAll (Gen.element ["det", "semidet"])
  secondDet <- forAll (Gen.element ["multi", "nondet"])
  reverseDecls <- forAll Gen.bool
  noIndex <- forAll Gen.bool
  let decls =
        [ "relation : " ++ firstDet ++ " (int: <=) (int: =>).",
          "relation : " ++ secondDet ++ " (int: =>) (int: <=)."
        ]
      source = unlines
        ([if noIndex then "<- noindex." else "<- index."]
         ++ (if reverseDecls then reverse decls else decls)
         ++ ["relation " ++ show n ++ " " ++ show key ++ "." | n <- [low, low + 1]]
         ++ ["helper" ++ show depth ++ " X <- relation X " ++ show key ++ "."]
         ++ ["helper" ++ show i ++ " X <- helper" ++ show (i + 1) ++ " X." | i <- [0 .. depth - 1]])
  program <- load source
  result <- equivalent program "helper0 X?"
  expectAnswers result ["X = " ++ show low, "X = " ++ show (low + 1)]
  -- Both signatures are applicable here; preserve first-match commitment.
  grounded <- equivalent program ("relation " ++ show low ++ " Y?")
  expectAnswers grounded ["Y = " ++ show key]

prop_generated_helper_dependencies :: Property
prop_generated_helper_dependencies = generated 150 $ do
  depth <- forAll (Gen.int (Range.linear 0 32))
  groundEnd <- forAll Gen.bool
  let terminal = if groundEnd then " <- X = 0." else "."
      source = helperChain depth terminal ++ unlines
        [ "select 0 first.",
          "select N second <- N != 0.",
          "wrapper R <- helper0 N, select N R."
        ]
  classify "longer than old ten-round bound" (depth > 10)
  classify "free helper result" (not groundEnd)
  program <- load source
  result <- equivalent program "wrapper R?"
  expectAnswers result (if groundEnd then ["R = first"] else ["R = first", "R = second"])

-- A bounded goal AST gives conjunction/disjunction/cut combinations useful
-- shrinking paths. Even the largest generated program has at most four
-- clauses, depth-two controls and a three-answer nonrecursive helper.
data SmallGoal
  = Succeed
  | Fail
  | BindX Term
  | BindR Term
  | Compare String Term
  | Alias
  | Choices
  | RestrictDomain
  | Arithmetic
  | Output
  | Missing
  | Cut
  | And SmallGoal SmallGoal
  | Or SmallGoal SmallGoal
  | If SmallGoal SmallGoal SmallGoal
  deriving (Show)

genGoal :: Int -> Gen SmallGoal
genGoal depth = Gen.choice $
  [ Gen.element [Succeed, Fail, Alias, Choices, RestrictDomain, Arithmetic, Output, Missing, Cut],
    BindX <$> genLiteral,
    BindR <$> genLiteral,
    Compare <$> genOperator <*> genLiteral
  ] ++ if depth <= 0 then [] else
    [ And <$> genGoal (depth - 1) <*> genGoal (depth - 1),
      Or <$> genGoal (depth - 1) <*> genGoal (depth - 1),
      If <$> genGoal (depth - 1) <*> genGoal (depth - 1) <*> genGoal (depth - 1)
    ]

renderGoal :: SmallGoal -> String
renderGoal goal = case goal of
  Succeed -> "true"
  Fail -> "fail"
  BindX term -> "X = " ++ show term
  BindR term -> "R = " ++ show term
  Compare operator term -> "X " ++ operator ++ " (" ++ show term ++ ")"
  Alias -> "R = X"
  Choices -> "choice R"
  RestrictDomain -> "X in 0..2"
  Arithmetic -> "R is X + 1"
  Output -> "write \"event\""
  Missing -> "missing X"
  Cut -> "!"
  And a b -> "(" ++ renderGoal a ++ ", " ++ renderGoal b ++ ")"
  Or a b -> "(" ++ renderGoal a ++ "; " ++ renderGoal b ++ ")"
  If a b c -> "(" ++ renderGoal a ++ " -> " ++ renderGoal b ++ " ; " ++ renderGoal c ++ ")"

prop_generated_finite_bodies :: Property
prop_generated_finite_bodies = generated 400 $ do
  clauses <- forAll (Gen.list (Range.linear 1 4) ((,) <$> Gen.maybe genLiteral <*> genGoal 2))
  actual <- forAll (Gen.maybe genLiteral)
  noIndex <- forAll Gen.bool
  let source = unlines $
        [ if noIndex then "<- noindex." else "<- index.",
          "p : unsafe.",
          "choice a.", "choice b.", "choice b."
        ] ++
        ["p " ++ maybe "X" show literal ++ " R <- " ++ renderGoal body ++ "." | (literal, body) <- clauses]
  program <- load source
  _ <- equivalent program ("p " ++ maybe "X" show actual ++ " R?")
  pure ()

prop_generated_tabling_and_indexing :: Property
prop_generated_tabling_and_indexing = generated 300 $ do
  count <- forAll (Gen.int (Range.linear 2 7))
  edges <- forAll (Gen.subsequence [(i, j) | i <- [0 .. count - 1], j <- [i + 1 .. count - 1]])
  table <- forAll Gen.bool
  index <- forAll Gen.bool
  start <- forAll (Gen.int (Range.linear 0 (count - 1)))
  let source = unlines $
        [ if index then "<- index." else "<- noindex.",
          if table then "path : table." else "path : notable.",
          "edge -1 -1.",
          "path X Y <- edge X Y.",
          "path X Y <- edge X Z, path Z Y.",
          "entry X Y <- path X Y."
        ] ++ ["edge " ++ show i ++ " " ++ show j ++ "." | (i, j) <- edges]
  program <- load source
  case lookupPred ("path", 2) program of
    Nothing -> failure
    Just predicate -> do
      predIsTabled program predicate === table
      predIsIndexed program predicate === index
  result <- equivalent program ("entry " ++ show start ++ " End?")
  summaryErrors result === []
  summaryExhausted result === False

prop_observable_results :: Property
prop_observable_results = unit $ do
  -- The oracle must actually encounter every observable category it compares.
  program <- load $ unlines
    [ "p : unsafe.",
      "p X <- X in 0..2, X != 1, write \"event\".",
      "p X <- missing X."
    ]
  result <- equivalent program "p X?"
  case summaryAnswers result of
    [answer] -> do
      assert (not (null (answerResiduals answer)))
      answerOutput answer === [WriteEvent "event"]
    _ -> failure
  summaryErrors result === [UnknownPredicate ("missing", 1)]
  summaryExhausted result === False
  -- A small explicit fuel budget avoids constructing 100,000 stack frames and
  -- observes incompleteness using the same evaluator and identical budgets.
  loop <- load "<- notable.\np ok.\np X <- loop X.\nloop X <- loop X."
  q <- query "p X?"
  let bounded prog = summarizeSearch q
        (solveGoals (mkEnv prog) 8 (initialState (queryNVars q)) (queryGoals q))
      boundedResult = bounded loop
  observe boundedResult === observe (bounded (withoutInferredPruning loop))
  map showAnswer (summaryAnswers boundedResult) === ["X = ok"]
  summaryExhausted boundedResult === True

inferenceGroup :: Group
inferenceGroup = Group "Inferred pruning preserves execution"
  [ ("alternative declared modes regression", prop_alternative_modes_regression),
    ("long groundness dependency regression", prop_groundness_chain_regression),
    ("integer vs float term equality regression", prop_mixed_numeric_term_regression),
    ("atom string character lexical guard regressions", prop_lexical_guards_regression),
    ("aliased call arguments retain both guarded answers", prop_call_alias_regressions),
    ("scalar and open tail labeling do not imply groundness", prop_open_label_groundness_regressions),
    ("NaN swapped guards use a consistent numeric ordering", prop_nan_swapped_guards_regression),
    ("generated numeric ordering reflexivity and operand reversal", prop_numeric_order_laws),
    ("constraint does not bind arithmetic input regression", prop_arithmetic_input_regression),
    ("positive conditional semidet optimizations remain", prop_positive_optimizations),
    ("generated literal guards vs unpruned execution", prop_generated_literal_guards),
    ("generated aliased nested head paths vs unpruned execution", prop_generated_head_paths),
    ("generated declared alternatives vs unpruned execution", prop_generated_declared_modes),
    ("generated helper dependencies vs unpruned execution", prop_generated_helper_dependencies),
    ("generated finite bodies cuts errors effects vs unpruned execution", prop_generated_finite_bodies),
    ("generated table and index policies vs unpruned execution", prop_generated_tabling_and_indexing),
    ("residual output error exhaustion observation", prop_observable_results)
  ]
