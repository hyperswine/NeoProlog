{-# LANGUAGE OverloadedStrings #-}

-- Independent bounded models, rather than another call to the interpreter,
-- serve as the oracles. All inputs are structural Hedgehog generators so a
-- failing case shrinks to a small term, graph, constraint or source buffer.
module CorrectnessTest (correctnessGroup) where

import Control.Exception (evaluate)
import Data.Char (ord)
import Data.List (intercalate, nub, sort)
import qualified Data.Set as Set
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera

generated :: PropertyT IO () -> Property
generated = withTests 300 . property

chars :: String -> Gen Char
chars = Gen.element

genTerm :: Int -> Gen Term
genTerm depth = Gen.choice $ leaves ++ if depth <= 0 then [] else
  [ Compound <$> Gen.element ["node", "pair", "branch"]
      <*> Gen.list (Range.linear 1 3) (genTerm (depth - 1)),
    (`mkList` Nothing) <$> Gen.list (Range.linear 0 3) (genTerm (depth - 1))
  ]
  where
    leaves =
      [ Var <$> Gen.int (Range.linear 0 5),
        IntLit <$> Gen.integral (Range.linear (-10) 10),
        Atom <$> Gen.element ["red", "blue", "nil"],
        StrLit <$> Gen.string (Range.linear 0 8) (chars "ab\t\n\"\\λ😀"),
        CharLit <$> chars "az\t\n\"'\\λ😀"
      ]

-- A textbook equation-elimination unifier, using eager tree replacement and
-- association lists. It shares neither dereferencing nor substitution code
-- with Infera.Unify.
referenceUnify :: Term -> Term -> Maybe [(VarId, Term)]
referenceUnify a b = go [] [(a, b)]
  where
    go bindings [] = Just bindings
    go bindings ((x, y) : rest)
      | x == y = go bindings rest
    go bindings ((Var v, t) : rest) = bind bindings rest v t
    go bindings ((t, Var v) : rest) = bind bindings rest v t
    go bindings ((Compound f xs, Compound g ys) : rest)
      | f == g && length xs == length ys = go bindings (zip xs ys ++ rest)
    go _ _ = Nothing
    bind bindings rest v t
      | v `elem` free t = Nothing
      | otherwise = go ((v, t) : [(w, replace v t u) | (w, u) <- bindings])
          [(replace v t x, replace v t y) | (x, y) <- rest]
    free (Var v) = [v]
    free (Compound _ xs) = concatMap free xs
    free _ = []
    replace v t (Var w) | v == w = t
    replace v t (Compound f xs) = Compound f (map (replace v t) xs)
    replace _ _ u = u

referenceWalk :: [(VarId, Term)] -> Term -> Term
referenceWalk bindings (Var v) = maybe (Var v) (referenceWalk bindings) (lookup v bindings)
referenceWalk bindings (Compound f xs) = Compound f (map (referenceWalk bindings) xs)
referenceWalk _ t = t

prop_unification_model :: Property
prop_unification_model = generated $ do
  a <- forAll (genTerm 2)
  b <- forAll (genTerm 2)
  let actual = unifyPlain emptySubst a b
      expected = referenceUnify a b
  cover 10 "unifiable" (case expected of Just _ -> True; _ -> False)
  cover 10 "not unifiable" (expected == Nothing)
  case (actual, expected) of
    (Nothing, Nothing) -> success
    (Just subst, Just bindings) -> do
      deepWalk subst a === deepWalk subst b
      deepWalk subst (deepWalk subst a) === deepWalk subst a
      -- Compare most-general results modulo free-variable naming, not just
      -- success/failure (an over-specialising unifier would otherwise pass).
      let pair = Compound "pair" [a, b]
      fst (canonicalize emptySubst (deepWalk subst pair))
        === fst (canonicalize emptySubst (referenceWalk bindings pair))
    _ -> annotateShow expected >> annotateShow actual >> failure

prop_unification_renaming :: Property
prop_unification_renaming = generated $ do
  a <- forAll (genTerm 2)
  b <- forAll (genTerm 2)
  offset <- forAll (Gen.int (Range.linear 1 100))
  let normalized x y = case unifyPlain emptySubst x y of
        Nothing -> Nothing
        Just s -> Just (fst (canonicalize s (Compound "pair" [x, y])))
  normalized a b === normalized (renameTerm offset a) (renameTerm offset b)
  -- Swapping arguments must preserve the same relation on both originals.
  case (unifyPlain emptySubst a b, unifyPlain emptySubst b a) of
    (Nothing, Nothing) -> success
    (Just s, Just t) ->
      fst (canonicalize s (Compound "pair" [a, b]))
        === fst (canonicalize t (Compound "pair" [a, b]))
    _ -> failure

prop_unification_ground_instance :: Property
prop_unification_ground_instance = generated $ do
  term <- forAll (genTerm 3)
  values <- forAll (Gen.list (Range.singleton 6) (Gen.integral (Range.linear (-20) 20)))
  let ground (Var v) = IntLit (values !! v)
      ground (Compound f xs) = Compound f (map ground xs)
      ground t = t
  case unifyPlain emptySubst term (ground term) of
    Nothing -> failure
    Just s -> deepWalk s term === ground term

prop_occurs_check_nested :: Property
prop_occurs_check_nested = generated $ do
  v <- forAll (Gen.int (Range.linear 0 20))
  depth <- forAll (Gen.int (Range.linear 1 12))
  let term = iterate (\t -> Compound "node" [IntLit 1, t]) (Var v) !! depth
  unifyPlain emptySubst (Var v) term === Nothing
  unifyPlain emptySubst term (Var v) === Nothing

prop_canonicalization :: Property
prop_canonicalization = generated $ do
  term <- forAll (genTerm 3)
  offset <- forAll (Gen.int (Range.linear 1 100))
  let (canonical, original) = canonicalize emptySubst term
  termVars canonical === [0 .. length original - 1]
  fst (canonicalize emptySubst canonical) === canonical
  fst (canonicalize emptySubst (renameTerm offset term)) === canonical
  -- Use the public instantiate operation, then independently restore names.
  let restore (Var v) = Var (original !! (v - offset))
      restore (Compound f xs) = Compound f (map restore xs)
      restore t = t
  restore (instantiate offset canonical) === term

prop_term_print_parse :: Property
prop_term_print_parse = generated $ do
  term <- forAll (genTerm 3)
  annotate (show term)
  parseTerm (show term) === Right (fst (canonicalize emptySubst term))

prop_literal_escape_regressions :: Property
prop_literal_escape_regressions = withTests 1 $ property $ do
  mapM_ (\c -> do
      annotateShow c
      parseTerm (show (CharLit c)) === Right (CharLit c)
      -- Digits following a numeric escape need a separator in the printer.
      let text = StrLit [c, '1', '\\', '"', '\n']
      parseTerm (show text) === Right text
    ) (['\0' .. '\127'] ++ "λ😀")

prop_parser_arbitrary_input :: Property
prop_parser_arbitrary_input = generated $ do
  source <- forAll $ Gen.choice
    [ Gen.string (Range.linear 0 150) Gen.unicode,
      Gen.string (Range.linear 0 150) (chars "abcXYZ_012 #!<>=.,?[]()|:+-*/\t\r\n\"'\\😀")
    ]
  -- Force the entire success or error value. Merely constructing Either or
  -- binding a lazy length would not detect parser exceptions.
  _ <- evalIO $ evaluate $ length (show (parseTerm source))
    + length (show (parseFile source))
    + length (show (parseLocatedFile "buffer.nprolog" source))
  success

-- ---------------------------------------------------------------------------
-- Finite integer constraints: at most 5^3 assignments, evaluated in Haskell.
-- ---------------------------------------------------------------------------

data Expr = Variable Int | Constant Integer | Add Expr Expr | Sub Expr Expr
  | Mul Expr Expr | Absolute Expr deriving (Eq, Show)

genExpr :: Int -> Gen Expr
genExpr depth = Gen.choice $ base ++ if depth <= 0 then [] else
  [ Add <$> child <*> child, Sub <$> child <*> child,
    Mul <$> child <*> child, Absolute <$> child ]
  where
    base = [Variable <$> Gen.int (Range.linear 0 2),
            Constant <$> Gen.integral (Range.linear (-4) 4)]
    child = genExpr (depth - 1)

evalExpr :: [Integer] -> Expr -> Integer
evalExpr env expr = case expr of
  Variable i -> env !! i
  Constant n -> n
  Add a b -> evalExpr env a + evalExpr env b
  Sub a b -> evalExpr env a - evalExpr env b
  Mul a b -> evalExpr env a * evalExpr env b
  Absolute a -> abs (evalExpr env a)

renderExpr :: Expr -> String
renderExpr expr = case expr of
  Variable i -> names !! i
  Constant n -> show n
  Add a b -> binary "+" a b
  Sub a b -> binary "-" a b
  Mul a b -> binary "*" a b
  Absolute a -> "abs (" ++ renderExpr a ++ ")"
  where binary op a b = "(" ++ renderExpr a ++ " " ++ op ++ " " ++ renderExpr b ++ ")"

expressionTerm :: Expr -> Term
expressionTerm expr = case expr of
  Variable i -> Var i
  Constant n -> IntLit n
  Add a b -> Compound "plus" [expressionTerm a, expressionTerm b]
  Sub a b -> Compound "minus" [expressionTerm a, expressionTerm b]
  Mul a b -> Compound "mul" [expressionTerm a, expressionTerm b]
  Absolute a -> Compound "abs" [expressionTerm a]

prop_arithmetic_model :: Property
prop_arithmetic_model = generated $ do
  expr <- forAll (genExpr 3)
  env <- forAll (Gen.list (Range.singleton 3) (Gen.integral (Range.linear (-20) 20)))
  let term = expressionTerm expr
      canonical = fst (canonicalize emptySubst term)
      bindings = [name ++ " = " ++ show value | (name, value) <- zip names env]
  parseTerm (show term) === Right canonical
  answers <- solve "" (intercalate ", " (bindings ++ ["Result is " ++ renderExpr expr]) ++ "?")
  case answers of
    [answer] -> integerBindings ["Result"] answer >>= (=== [evalExpr env expr])
    _ -> failure

prop_domain_holes_and_large_integers :: Property
prop_domain_holes_and_large_integers = generated $ do
  origin <- forAll (Gen.element [0, 10 ^ (40 :: Int), negate (10 ^ (40 :: Int))])
  shift <- forAll (Gen.integral (Range.linear (-10) 10))
  width <- forAll (Gen.integral (Range.linear 0 8))
  holes <- forAll (Gen.list (Range.linear 0 12) (Gen.integral (Range.linear (-1) (width + 1))))
  let lo = origin + shift
      hi = lo + width
      excluded = map (+ lo) holes
      goals = ["X in " ++ show lo ++ ".." ++ show hi]
        ++ ["X #!= " ++ show value | value <- excluded]
      feasible = [value | value <- [lo .. hi], value `notElem` excluded]
  classify "large integer" (origin /= 0)
  cover 5 "empty domain" (null feasible)
  mapM_ (\(final, expected) -> do
      answers <- solve "" (intercalate ", " (goals ++ [final]) ++ "?")
      actual <- mapM (integerBindings ["X"]) answers
      actual === map (: []) expected
    ) [("label [X]", feasible), ("labeling [min X] [X]", take 1 feasible),
       ("minimize X (label [X])", take 1 feasible)]

names :: [String]
names = ["X", "Y", "Z"]

data Relation = Equal | Different | Less | LessEqual | Greater | GreaterEqual
  deriving (Eq, Show, Enum, Bounded)

holds :: Relation -> Integer -> Integer -> Bool
holds rel = case rel of
  Equal -> (==); Different -> (/=); Less -> (<); LessEqual -> (<=)
  Greater -> (>); GreaterEqual -> (>=)

operator :: Relation -> String
operator rel = case rel of
  Equal -> "#="; Different -> "#!="; Less -> "#<"; LessEqual -> "#<="
  Greater -> "#>"; GreaterEqual -> "#>="

data Model = Model [(Integer, Integer)] [(Expr, Relation, Expr)] Bool Bool
  deriving Show

genModel :: Gen Model
genModel = do
  domains <- Gen.list (Range.singleton 3) $ do
    lo <- Gen.integral (Range.linear (-3) 2)
    width <- Gen.integral (Range.linear 0 4)
    pure (lo, lo + width)
  constraints <- Gen.list (Range.linear 0 3) $
    (,,) <$> genExpr 2 <*> Gen.enumBounded <*> genExpr 1
  Model domains constraints <$> Gen.bool <*> Gen.bool

solutions :: Model -> [[Integer]]
solutions (Model domains constraints distinct alias) =
  [ env | env <- sequence [[lo .. hi] | (lo, hi) <- domains],
    all (\(a, r, b) -> holds r (evalExpr env a) (evalExpr env b)) constraints,
    not distinct || length (nub env) == length env,
    not alias || env !! 0 == env !! 1 ]

modelGoals :: Model -> [String]
modelGoals (Model domains constraints distinct alias) =
  [name ++ " in " ++ show lo ++ ".." ++ show hi | (name, (lo, hi)) <- zip names domains]
  ++ [renderExpr a ++ " " ++ operator r ++ " " ++ renderExpr b | (a, r, b) <- constraints]
  ++ ["all_different [X, Y, Z]" | distinct]
  ++ ["X = Y" | alias]

solve :: String -> String -> PropertyT IO [Answer]
solve source query = do
  annotate query
  prog <- evalEither (loadProgramText source)
  q <- evalEither (parseQuery query)
  let summary = solveAll prog q
  summaryErrors summary === []
  summaryExhausted summary === False
  pure (summaryAnswers summary)

integerBindings :: [String] -> Answer -> PropertyT IO [Integer]
integerBindings vars answer = mapM get vars
  where get name = case lookup name (answerBindings answer) of
          Just (IntLit n) -> pure n
          other -> annotateShow (name, other, answer) >> failure

finiteAnswers :: [String] -> String -> PropertyT IO [[Integer]]
finiteAnswers goals final = do
  answers <- solve "" (intercalate ", " (goals ++ [final]) ++ "?")
  sort <$> mapM (integerBindings names) answers

labelModel :: Model -> PropertyT IO ()
labelModel model@(Model domains constraints distinct alias) = do
  cover 5 "no solutions" (null (solutions model))
  cover 5 "has solutions" (not (null (solutions model)))
  classify "negative domains" (any ((< 0) . fst) domains)
  classify "all different" distinct
  classify "aliased variables" alias
  classify "nonlinear constraints" (any (\(a, _, b) -> nonlinear a || nonlinear b) constraints)
  where
    nonlinear (Mul _ _) = True
    nonlinear (Absolute _) = True
    nonlinear (Add a b) = nonlinear a || nonlinear b
    nonlinear (Sub a b) = nonlinear a || nonlinear b
    nonlinear _ = False

prop_clp_model :: Property
prop_clp_model = generated $ do
  model <- forAll genModel
  labelModel model
  actual <- finiteAnswers (modelGoals model) "label [X, Y, Z]"
  actual === sort (solutions model)

prop_clp_order_independent :: Property
prop_clp_order_independent = generated $ do
  model <- forAll genModel
  shuffled <- forAll (Gen.shuffle (modelGoals model))
  variables <- forAll (Gen.shuffle names)
  actual <- finiteAnswers shuffled ("label [" ++ intercalate ", " variables ++ "]")
  actual === sort (solutions model)

prop_minimum_model :: Property
prop_minimum_model = generated $ do
  model <- forAll genModel
  cost <- forAll (genExpr 2)
  labelModel model
  let feasible = solutions model
      goals = modelGoals model
      objective = renderExpr cost
  mapM_ (\final -> do
      actual <- finiteAnswers goals final
      case feasible of
        [] -> actual === []
        _ -> case actual of
          [env] -> do
            assert (env `elem` feasible)
            evalExpr env cost === minimum (map (`evalExpr` cost) feasible)
          _ -> failure
    ) ["labeling [min (" ++ objective ++ ")] [X, Y, Z]",
       "minimize (" ++ objective ++ ") (label [X, Y, Z])"]

prop_minimize_ties_and_output :: Property
prop_minimize_ties_and_output = generated $ do
  costs <- forAll (Gen.list (Range.linear 1 20) (Gen.integral (Range.linear (-4) 4) :: Gen Integer))
  let source = unlines ["choice " ++ show i ++ " " ++ show cost ++ "." | (i, cost) <- zip [0 :: Int ..] costs]
      expected = snd (minimum [(cost, i) | (i, cost) <- zip [0 :: Integer ..] costs])
  answers <- solve source "minimize C (choice I C, write I)?"
  case answers of
    [answer] -> do
      integerBindings ["I", "C"] answer >>= (=== [expected, minimum costs])
      concatMap renderOutputEvent (answerOutput answer) === show expected
    _ -> failure

-- ---------------------------------------------------------------------------
-- Tabling and indexing, compared with ordinary finite data structures.
-- ---------------------------------------------------------------------------

prop_tabling_graph_model :: Property
prop_tabling_graph_model = generated $ do
  size <- forAll (Gen.int (Range.linear 1 5))
  edges <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  start <- forAll (Gen.int (Range.linear 0 (size - 1)))
  cover 5 "self loop" (any (uncurry (==)) edges)
  classify "empty graph" (null edges)
  let node i = "n" ++ show i
      source = unlines $
        ["edge _ _ <- fail."]
        ++ ["edge " ++ node a ++ " " ++ node b ++ "." | (a, b) <- edges]
        ++ ["path X Y <- path X Z, edge Z Y.", "path X Y <- edge X Y."]
      step reached = Set.union reached (Set.fromList [b | (a, b) <- edges, Set.member a reached])
      closure reached = let next = step reached in if next == reached then reached else closure next
      expected = sort (map (Atom . node) (Set.toList (closure (Set.fromList [b | (a, b) <- edges, a == start]))))
  answers <- solve source ("path " ++ node start ++ " Target?")
  let actual = [t | answer <- answers, Just t <- [lookup "Target" (answerBindings answer)]]
  sort actual === expected -- also rejects duplicate tabled answers

prop_indexing_model :: Property
prop_indexing_model = generated $ do
  facts <- forAll (Gen.list (Range.linear 0 25) ((,) <$> Gen.int (Range.linear 0 3) <*> Gen.integral (Range.linear (-5) 5)))
  selected <- forAll (Gen.int (Range.linear 0 3))
  let atom i = "key" ++ show i
      source = unlines (["item _ _ <- fail."] ++ ["item " ++ atom key ++ " " ++ show n ++ "." | (key, n) <- facts])
      query = "item " ++ atom selected ++ " Value?"
      expected = [n | (key, n) <- facts, key == selected]
  mapM_ (\prefix -> do
      answers <- solve (prefix ++ source) query
      actual <- mapM (integerBindings ["Value"]) answers
      actual === map (: []) expected -- retain order and duplicate facts
    ) ["", "item : noindex (any) (any).\n"]

-- ---------------------------------------------------------------------------
-- Diagnostic contracts and UTF-16 ranges for generated live-buffer contents.
-- ---------------------------------------------------------------------------

located :: String -> PropertyT IO [LocatedTopLevel]
located source = case parseLocatedFile "buffer.nprolog" source of
  Left err -> annotateShow err >> failure
  Right items -> pure items

utf16Position :: String -> (Int, Int)
utf16Position source = (length (filter (== '\n') source) + 1,
  1 + sum [if ord c > 0xffff then 2 else 1 | c <- reverse (takeWhile (/= '\n') (reverse source))])

prop_diagnostic_locations :: Property
prop_diagnostic_locations = generated $ do
  comments <- forAll (Gen.list (Range.linear 0 8) (Gen.string (Range.linear 0 20) (chars "abc\tλ😀")))
  text <- forAll (Gen.string (Range.linear 0 20) (chars "abcλ😀"))
  indent <- forAll (Gen.string (Range.linear 0 8) (chars " \t"))
  newline <- forAll (Gen.element ["\n", "\r\n"])
  gap <- forAll (Gen.element [" ", "\t", "\n\t", " # 😀\n  "])
  let prefix = concatMap (\c -> "# " ++ c ++ newline) comments ++ indent
      item = "entry \"" ++ text ++ "\"" ++ gap ++ "<- absent 1."
      source = prefix ++ item ++ " # trailing 😀\n\t"
      (line, col) = utf16Position prefix
      (endLine, endCol) = utf16Position (prefix ++ item)
      expected = SourceSpan "buffer.nprolog" line col endLine endCol
  items <- located source
  map locatedSpan items === [expected]
  map locatedItem items === either (const []) id (parseFile source)
  case diagnose items of
    [d] -> do
      diagnosticSpan d === expected
      diagnosticCode d === "undefined-predicate"
      diagnosticSeverity d === Error
    ds -> annotateShow ds >> failure

prop_diagnostic_arity_model :: Property
prop_diagnostic_arity_model = generated $ do
  defined <- forAll (Gen.subsequence [0 .. 5 :: Int])
  called <- forAll (Gen.int (Range.linear 0 6))
  wrapperIndex <- forAll (Gen.int (Range.constant 0 5))
  let wrapper = [id, (\g -> "once (" ++ g ++ ")"),
        (\g -> "not (" ++ g ++ ")"), (\g -> "findall 1 (" ++ g ++ ") _"),
        (\g -> "minimize 1 (" ++ g ++ ")"), (\g -> "call (" ++ g ++ ")")] !! wrapperIndex
      goal n = "target" ++ concat (replicate n " 1")
      source = unlines [goal n ++ "." | n <- defined]
        ++ "entry <- " ++ wrapper (goal called) ++ "."
      expected | called `elem` defined = []
               | null defined = ["undefined-predicate"]
               | otherwise = ["wrong-arity"]
  ds <- diagnose <$> located source
  map diagnosticCode ds === expected

prop_diagnostic_renaming :: Property
prop_diagnostic_renaming = generated $ do
  singleton <- forAll Gen.bool
  hidden <- forAll Gen.bool
  suffix <- forAll (Gen.string (Range.linear 0 10) (chars "abcdef0123"))
  let name = (if hidden then "_Value" else "Value") ++ suffix
      source variable = "entry " ++ variable ++ " <- "
        ++ (if singleton then "absent 1." else "absent " ++ variable ++ ".")
  ds <- diagnose <$> located (source name)
  map diagnosticCode ds === ["undefined-predicate"] ++ ["singleton-variable" | singleton && not hidden]

prop_diagnostic_sort_model :: Property
prop_diagnostic_sort_model = generated $ do
  declared <- forAll (Gen.element [SAny, SInt, SNum, SFloat, SStr, SChar, SAtom, SList SInt])
  argument <- forAll (Gen.element
    [ ("3", [SInt, SNum]), ("2.5", [SFloat, SNum]), ("red", [SAtom]),
      ("\"text\"", [SStr]), ("'a'", [SChar]), ("[1, 2]", [SList SInt]),
      ("[1, red]", []), ("3 + 4", [SInt, SNum]), ("_Open", []) ])
  let (literal, sorts) = argument
      source = "target : nondet (" ++ showSort declared ++ ": <=>).\ntarget _.\nentry <- target (" ++ literal ++ ")."
      compatible = declared == SAny || declared `elem` sorts || literal == "_Open"
  ds <- diagnose <$> located source
  map diagnosticCode ds === ["call-sort-mismatch" | not compatible]

correctnessGroup :: Group
correctnessGroup = Group "Generated correctness models"
  [ ("unification vs equation elimination", prop_unification_model),
    ("unification symmetry and renaming", prop_unification_renaming),
    ("unification ground instances", prop_unification_ground_instance),
    ("nested occurs check", prop_occurs_check_nested),
    ("canonicalization and instantiation", prop_canonicalization),
    ("recursive term print/parse roundtrip", prop_term_print_parse),
    ("literal escape regressions", prop_literal_escape_regressions),
    ("fully evaluated arbitrary parser input", prop_parser_arbitrary_input),
    ("arithmetic printer and evaluation vs integer model", prop_arithmetic_model),
    ("domain holes and arbitrary-precision boundaries", prop_domain_holes_and_large_integers),
    ("CLP vs finite integer model", prop_clp_model),
    ("constraint and labeling order independence", prop_clp_order_independent),
    ("both optimizers vs finite integer model", prop_minimum_model),
    ("minimum ties and isolated output", prop_minimize_ties_and_output),
    ("tabled reachability vs graph closure", prop_tabling_graph_model),
    ("indexing vs ordered fact model", prop_indexing_model),
    ("diagnostic UTF-16 locations", prop_diagnostic_locations),
    ("diagnostic arities through meta goals", prop_diagnostic_arity_model),
    ("diagnostic variable naming", prop_diagnostic_renaming),
    ("diagnostic sorts vs literal model", prop_diagnostic_sort_model)
  ]
