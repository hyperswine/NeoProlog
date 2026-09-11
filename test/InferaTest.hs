{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module InferaTest (inferaGroup) where

import Data.List (isInfixOf, isPrefixOf, sort)
import qualified Data.Map.Strict as Map
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera
import System.Directory (getTemporaryDirectory)
import System.FilePath ((</>))

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

-- Run a query against program text; answers rendered as strings.
run :: String -> String -> [String]
run prog q = case runInfera prog q of
  Left err -> ["PARSE ERROR: " ++ err]
  Right xs -> xs

assertAnswers :: String -> String -> [String] -> PropertyT IO ()
assertAnswers prog q expected = do
  annotate q
  run prog q === expected

assertFirst :: String -> String -> String -> PropertyT IO ()
assertFirst prog q expected = do
  annotate q
  case run prog q of
    (x : _) -> x === expected
    [] -> failure

assertErrorContains :: String -> String -> String -> PropertyT IO ()
assertErrorContains prog q needle = do
  annotate q
  case run prog q of
    (x : _) -> do
      annotate x
      assert ("Error:" `isPrefixOf` x && needle `isInfixOf` x)
    [] -> failure

loadOrFail :: String -> PropertyT IO Program
loadOrFail src = case loadProgramText src of
  Left err -> annotate err >> failure
  Right p -> pure p

predOrFail :: Program -> PredKey -> PropertyT IO Pred
predOrFail prog k = case lookupPred k prog of
  Nothing -> annotate ("missing predicate " ++ show k) >> failure
  Just p -> pure p

-- ---------------------------------------------------------------------------
-- Programs used by several tests
-- ---------------------------------------------------------------------------

listsProg :: String
listsProg =
  unlines
    [ "append [] L L.",
      "append [H | T] L [H | R] <- append T L R.",
      "member X [X | _].",
      "member X [_ | T] <- member X T.",
      "length [] 0.",
      "length [_ | T] N <- length T N1, N is N1 + 1.",
      "reverse [] [].",
      "reverse [H | T] R <- reverse T RT, append RT [H] R."
    ]

factProg :: String
factProg =
  unlines
    [ "factorial 0 1.",
      "factorial N R <- N > 0, R = R2 * N, factorial (N - 1) R2."
    ]

colorsProg :: String
colorsProg = unlines ["color red.", "color green.", "color blue."]

genAtomName :: Gen String
genAtomName = do
  c <- Gen.element ['a' .. 'z']
  cs <- Gen.list (Range.linear 0 8) (Gen.element (['a' .. 'z'] ++ ['0' .. '9'] ++ "_"))
  pure (c : cs)

genSmallInt :: Gen Integer
genSmallInt = Gen.integral (Range.linear 0 50)

-- ---------------------------------------------------------------------------
-- Parser
-- ---------------------------------------------------------------------------

prop_parse_atom :: Property
prop_parse_atom = property $ do
  name <- forAll genAtomName
  case parseTerm name of
    Right (Atom a) | name `notElem` ["is", "in"] -> a === name
    Right _ -> success
    Left err -> annotate err >> failure

prop_parse_int :: Property
prop_parse_int = property $ do
  n <- forAll (Gen.integral (Range.linear (-9999) 9999))
  case parseTerm (show n) of
    Right (IntLit m) -> m === n
    _ -> failure

prop_parse_var_is_numbered :: Property
prop_parse_var_is_numbered = unit $ do
  parseTerm "X" === Right (Var 0)
  parseTerm "foo X Y X" === Right (Compound "foo" [Var 0, Var 1, Var 0])
  -- anonymous variables are all distinct
  parseTerm "foo _ _" === Right (Compound "foo" [Var 0, Var 1])

prop_parse_list_is_cons :: Property
prop_parse_list_is_cons = unit $ do
  parseTerm "[1, 2]" === Right (cons (IntLit 1) (cons (IntLit 2) nil))
  parseTerm "[1 | T]" === Right (cons (IntLit 1) (Var 0))
  parseTerm "1 :: T" === Right (cons (IntLit 1) (Var 0))
  parseTerm "[]" === Right nil

prop_parse_arith :: Property
prop_parse_arith = property $ do
  a <- forAll genSmallInt
  b <- forAll genSmallInt
  c <- forAll genSmallInt
  parseTerm (show a ++ " + " ++ show b ++ " * " ++ show c)
    === Right (Compound "plus" [IntLit a, Compound "mul" [IntLit b, IntLit c]])

prop_parse_operators :: Property
prop_parse_operators = unit $ do
  parseTerm "1 >= 2" === Right (Compound "gte" [IntLit 1, IntLit 2])
  parseTerm "1 <= 2" === Right (Compound "lte" [IntLit 1, IntLit 2])
  parseTerm "X = 2" === Right (Compound "unify" [Var 0, IntLit 2])
  parseTerm "X #= 2" === Right (Compound "int_eq" [Var 0, IntLit 2])
  parseTerm "X #!= 2" === Right (Compound "fd_ne" [Var 0, IntLit 2])
  parseTerm "X in 1..9" === Right (Compound "in" [Var 0, Compound "range" [IntLit 1, IntLit 9]])
  parseTerm "(a -> b ; c)" === Right (Compound ";" [Compound "->" [Atom "a", Atom "b"], Atom "c"])

prop_parse_declaration :: Property
prop_parse_declaration = unit $ do
  parseFile "mypred : semidet (int: <=) (int: <=>) (str: =>)."
    === Right
      [ TLDecl
          ( Decl
              "mypred"
              (Just Semidet)
              []
              [ArgSpec SInt ModeIn, ArgSpec SInt ModeInOut, ArgSpec SStr ModeOut]
          )
      ]
  parseFile "fib : det notable (list int: <=) =>."
    === Right [TLDecl (Decl "fib" (Just Det) [FlagNoTable] [ArgSpec (SList SInt) ModeIn, ArgSpec SAny ModeOut])]
  parseFile "gen : notable." === Right [TLDecl (Decl "gen" Nothing [FlagNoTable] [])]

prop_parse_hash_comment :: Property
prop_parse_hash_comment = unit $ do
  parseFile "# a comment\nfoo 1. # trailing\n" === Right [TLClause (Clause (Compound "foo" [IntLit 1]) [] 0)]
  case parseFile "p X <- X #= 1 + 2." of
    Right [TLClause (Clause _ [Compound "int_eq" _] _)] -> success
    other -> annotateShow other >> failure

prop_parse_nocrash :: Property
prop_parse_nocrash = property $ do
  src <- forAll (Gen.string (Range.linear 0 40) Gen.unicode)
  _ <- pure (either length (const 0) (parseTerm src))
  success

prop_show_roundtrip :: Property
prop_show_roundtrip = unit $ do
  show (cons (IntLit 1) (cons (Atom "a") nil)) === "[1, a]"
  show (Compound "plus" [IntLit 1, Compound "mul" [IntLit 2, IntLit 3]]) === "1 + 2 * 3"
  show (Compound "mul" [Compound "plus" [IntLit 1, IntLit 2], IntLit 3]) === "(1 + 2) * 3"
  show (Compound "f" [Compound "g" [IntLit 1], Atom "b"]) === "f (g 1) b"

-- ---------------------------------------------------------------------------
-- Unification
-- ---------------------------------------------------------------------------

prop_unify_atoms :: Property
prop_unify_atoms = property $ do
  a <- forAll genAtomName
  b <- forAll genAtomName
  let r = unifyPlain emptySubst (Atom a) (Atom b)
  if a == b then r /== Nothing else r === Nothing

prop_unify_var_binds :: Property
prop_unify_var_binds = property $ do
  n <- forAll genSmallInt
  case unifyPlain emptySubst (Var 0) (IntLit n) of
    Just s -> deepWalk s (Var 0) === IntLit n
    Nothing -> failure

prop_unify_occurs_check :: Property
prop_unify_occurs_check = unit $ do
  unifyPlain emptySubst (Var 0) (Compound "f" [Var 0]) === Nothing

prop_unify_compound :: Property
prop_unify_compound = property $ do
  f <- forAll genAtomName
  a <- forAll genSmallInt
  case unifyPlain emptySubst (Compound f [Var 0, IntLit a]) (Compound f [IntLit a, Var 1]) of
    Just s -> do
      deepWalk s (Var 0) === IntLit a
      deepWalk s (Var 1) === IntLit a
    Nothing -> failure

prop_unify_prefers_older_variable :: Property
prop_unify_prefers_older_variable = unit $ do
  case unify emptySubst (Var 0) (Var 5) of
    Just (s, _) -> walk s (Var 5) === Var 0
    Nothing -> failure

-- ---------------------------------------------------------------------------
-- Core engine behaviour
-- ---------------------------------------------------------------------------

prop_engine_lists :: Property
prop_engine_lists = unit $ do
  assertAnswers listsProg "append [1, 2] [3] R?" ["R = [1, 2, 3]"]
  assertAnswers listsProg "append X Y [1, 2]?" ["X = [], Y = [1, 2]", "X = [1], Y = [2]", "X = [1, 2], Y = []"]
  assertAnswers listsProg "member X [a, b]?" ["X = a", "X = b"]
  assertAnswers listsProg "length [a, b, c] N?" ["N = 3"]
  assertAnswers listsProg "reverse [1, 2, 3] R?" ["R = [3, 2, 1]"]
  assertAnswers listsProg "member z [a, b]?" ["false."]

prop_engine_arith_in_heads :: Property
prop_engine_arith_in_heads = unit $ do
  assertAnswers factProg "factorial 5 R?" ["R = 120"]
  assertAnswers "" "X is 2 + 3 * 4?" ["X = 14"]
  assertAnswers "" "X is 7 / 2?" ["X = 3"]
  assertAnswers "" "X is 7.0 / 2?" ["X = 3.5"]
  assertAnswers "" "3 > 2, 2 >= 2, 1 < 2, 2 <= 2?" ["true."]
  assertErrorContains "" "X is Y + 1?" "not sufficiently instantiated"
  assertErrorContains "" "X is 1 / 0?" "division by zero"

prop_engine_cut :: Property
prop_engine_cut = unit $ do
  let prog =
        unlines
          [ "q 1.",
            "q 2.",
            "q 3.",
            "first X <- q X, !.",
            "first 0.",
            "s X <- q X, X > 5, !.",
            "s none.",
            "max3 A B A <- A >= B, !.",
            "max3 _ B B."
          ]
  assertAnswers prog "first X?" ["X = 1"]
  assertAnswers prog "s X?" ["X = none"]
  assertAnswers prog "max3 3 9 M?" ["M = 9"]
  assertAnswers prog "max3 9 3 M?" ["M = 9"]
  -- cut at the top level of a query
  assertAnswers prog "q X, !?" ["X = 1"]
  -- cut inside call/1 is local to the call
  assertAnswers prog "call (q X, !), q Y?" ["X = 1, Y = 1", "X = 1, Y = 2", "X = 1, Y = 3"]

prop_engine_control :: Property
prop_engine_control = unit $ do
  let prog = unlines ["sign N S <- (N > 0 -> S = pos ; N < 0 -> S = neg ; S = zero).", "q 1.", "q 2."]
  assertAnswers prog "sign 5 S?" ["S = pos"]
  assertAnswers prog "sign -5 S?" ["S = neg"]
  assertAnswers prog "sign 0 S?" ["S = zero"]
  assertAnswers prog "(q X ; X = 9)?" ["X = 1", "X = 2", "X = 9"]
  assertAnswers prog "not (q 3)?" ["true."]
  assertAnswers prog "not (q 1)?" ["false."]
  assertAnswers prog "once (q X)?" ["X = 1"]
  assertAnswers prog "findall X (q X) L?" ["L = [1, 2]"]
  assertAnswers prog "forall (q X) (X > 0)?" ["true."]
  assertAnswers prog "forall (q X) (X > 1)?" ["false."]
  assertErrorContains prog "nope 1?" "unknown predicate: nope/1"

prop_engine_disequality :: Property
prop_engine_disequality = unit $ do
  assertAnswers colorsProg "color X, X != red?" ["X = green", "X = blue"]
  assertAnswers "" "X != Y, X = 1, Y = 1?" ["false."]
  assertAnswers "" "X != Y, X = 1, Y = 2?" ["X = 1, Y = 2"]
  assertAnswers "" "X != 1?" ["X != 1"]

prop_engine_dcg :: Property
prop_engine_dcg = unit $ do
  let prog =
        unlines
          [ "greeting -> [hello], name.",
            "name -> [world].",
            "name -> [infera].",
            "ab -> [a], ab, [b].",
            "ab -> []."
          ]
  assertAnswers prog "phrase greeting [hello, world]?" ["true."]
  assertAnswers prog "greeting L []?" ["L = [hello, world]", "L = [hello, infera]"]
  assertAnswers prog "phrase ab [a, a, b, b]?" ["true."]
  assertAnswers prog "phrase ab [a, b, b]?" ["false."]

prop_engine_output :: Property
prop_engine_output = unit $ do
  assertAnswers "" "write hello, nl, write 42?" ["hello\n42", "true."]
  assertAnswers "" "write \"str\"?" ["str", "true."]

prop_engine_strings :: Property
prop_engine_strings = unit $ do
  assertAnswers "" "str_concat \"ab\" \"cd\" S?" ["S = \"abcd\""]
  assertAnswers "" "str_concat A B \"ab\"?" ["A = \"\", B = \"ab\"", "A = \"a\", B = \"b\"", "A = \"ab\", B = \"\""]
  assertAnswers "" "str_length \"abc\" N?" ["N = 3"]
  assertAnswers "" "str_chars \"ab\" L?" ["L = ['a', 'b']"]
  assertAnswers "" "str_num \"42\" N?" ["N = 42"]
  assertAnswers "" "is_list [1], is_int 3, is_str \"s\", var X, nonvar 1?" ["true."]

prop_engine_depth_limit :: Property
prop_engine_depth_limit = unit $ do
  let prog = "loop : notable.\nloop X <- loop X."
  assertAnswers prog "loop 1?" ["Search depth limit reached; the query was not proven false."]

-- ---------------------------------------------------------------------------
-- Declarations: modes, sorts, determinism
-- ---------------------------------------------------------------------------

declProg :: String
declProg =
  unlines
    [ "fact : det (int: <=) (int: =>).",
      "fact 0 1.",
      "fact N R <- N > 0, N1 is N - 1, fact N1 R1, R is N * R1.",
      "len : semidet (list any: <=) (int: =>).",
      "len [] 0.",
      "len [_ | T] N <- len T N1, N is N1 + 1.",
      "must_one : det (any: <=).",
      "must_one a.",
      "many : multi (any: =>).",
      "many 1.",
      "many 2.",
      "pick : semidet (atom: =>).",
      "pick red.",
      "pick green.",
      "bad_out : det (any: =>).",
      "bad_out _.",
      "greet : det (str: <=) (str: =>).",
      "greet N G <- str_concat \"hi \" N G."
    ]

prop_decl_modes_and_sorts :: Property
prop_decl_modes_and_sorts = unit $ do
  assertAnswers declProg "fact 5 R?" ["R = 120"]
  assertAnswers declProg "len [a, b] N?" ["N = 2"]
  assertErrorContains declProg "fact X 5?" "mode error: argument 1 of fact/2"
  assertErrorContains declProg "fact a R?" "sort error: argument 1 of fact/2 must be int"
  assertErrorContains declProg "len \"abc\" N?" "sort error: argument 1 of len/2 must be list any"
  assertErrorContains declProg "fact 3 x?" "sort error: argument 2 of fact/2 must be int"
  assertErrorContains declProg "bad_out X?" "declared output (=>) but is not ground"
  assertAnswers declProg "greet \"bob\" G?" ["G = \"hi bob\""]
  assertErrorContains declProg "greet 3 G?" "must be str"

prop_decl_determinism :: Property
prop_decl_determinism = unit $ do
  assertErrorContains declProg "must_one b?" "declared det but failed"
  assertAnswers declProg "many X?" ["X = 1", "X = 2"]
  -- semidet commits to the first solution
  assertAnswers declProg "pick C?" ["C = red"]
  let noMulti = "m : multi (any: =>).\nm 1 <- fail."
  assertErrorContains noMulti "m X?" "declared multi but failed"

prop_decl_multiple_modes :: Property
prop_decl_multiple_modes = unit $ do
  let prog =
        unlines
          [ "plus2 : det (int: <=) (int: =>).",
            "plus2 : det (int: =>) (int: <=).",
            "plus2 X Y <- nonvar X, !, Y is X + 2.",
            "plus2 X Y <- X is Y - 2."
          ]
  assertAnswers prog "plus2 1 Y?" ["Y = 3"]
  assertAnswers prog "plus2 X 5?" ["X = 3"]
  assertErrorContains prog "plus2 X Y?" "mode error"

-- ---------------------------------------------------------------------------
-- Inference
-- ---------------------------------------------------------------------------

prop_infer_signatures :: Property
prop_infer_signatures = unit $ do
  prog <- loadOrFail (listsProg ++ factProg)
  len <- predOrFail prog ("length", 2)
  let sig = predInferred len
  sigDet sig === Semidet
  sigSwitch sig === [0]
  map argSort (sigArgs sig) === [SList SAny, SNum]
  map argMode (sigArgs sig) === [ModeInOut, ModeOut]
  app <- predOrFail prog ("append", 3)
  sigDet (predInferred app) === Semidet
  sigSwitch (predInferred app) === [0]
  mem <- predOrFail prog ("member", 2)
  sigDet (predInferred mem) === Nondet
  fact <- predOrFail prog ("factorial", 2)
  sigDet (predInferred fact) === Semidet
  map argMode (sigArgs (predInferred fact)) === [ModeIn, ModeOut]

prop_infer_guards :: Property
prop_infer_guards = unit $ do
  prog <-
    loadOrFail $
      unlines
        [ "max2 A B A <- A >= B.",
          "max2 A B B <- B > A.",
          "zflag 0 1.",
          "zflag V 0 <- V != 0.",
          "fib 0 0.",
          "fib 1 1.",
          "fib N F <- N > 1, N1 is N - 1, N2 is N - 2, fib N1 F1, fib N2 F2, F is F1 + F2.",
          "between Lo Hi Lo <- Lo <= Hi.",
          "between Lo Hi X <- Lo < Hi, Lo1 is Lo + 1, between Lo1 Hi X."
        ]
  let det k = sigDet . predInferred <$> predOrFail prog k
  det ("max2", 3) >>= (=== Semidet)
  det ("zflag", 2) >>= (=== Semidet)
  det ("fib", 2) >>= (=== Semidet)
  det ("between", 3) >>= (=== Nondet)
  zf <- predOrFail prog ("zflag", 2)
  -- != guards only exclude when the argument is ground
  sigSwitch (predInferred zf) === [0]

-- The inferred semidet commit must never lose solutions.
prop_infer_commit_is_sound :: Property
prop_infer_commit_is_sound = unit $ do
  -- partial list: length is genuinely nondeterministic here (a generator,
  -- so it must not be tabled)
  assertFirst listsProg "length [a | T] N?" "T = [], N = 1"
  assertAnswers "zflag 0 1.\nzflag V 0 <- V != 0." "zflag V Z?" ["V = 0, Z = 1", "Z = 0, V != 0"]

prop_infer_tabling_defaults :: Property
prop_infer_tabling_defaults = unit $ do
  prog <-
    loadOrFail $
      unlines
        [ "edge a b.",
          "path X Y <- path X Z, edge Z Y.",
          "path X Y <- edge X Y.",
          "noisy N <- write N, noisy N.",
          "quiet : notable.",
          "quiet X <- quiet X.",
          "forced : table (any: <=).",
          "forced 1."
        ]
  let tabled k = predIsTabled prog <$> predOrFail prog k
  tabled ("path", 2) >>= (=== True)
  -- structural recursion (list walking) is not tabled by default
  lists <- loadOrFail listsProg
  predIsTabled lists <$> predOrFail lists ("length", 2) >>= (=== False)
  predIsTabled lists <$> predOrFail lists ("append", 3) >>= (=== False)
  fibP <- loadOrFail "fib 0 0.\nfib 1 1.\nfib N F <- N > 1, N1 is N - 1, N2 is N - 2, fib N1 F1, fib N2 F2, F is F1 + F2."
  predIsTabled fibP <$> predOrFail fibP ("fib", 2) >>= (=== True)
  tabled ("edge", 2) >>= (=== False)
  tabled ("noisy", 1) >>= (=== False)
  tabled ("quiet", 1) >>= (=== False)
  tabled ("forced", 1) >>= (=== True)
  p <- predOrFail prog ("noisy", 1)
  predPure p === False
  predRecursive p === True

-- ---------------------------------------------------------------------------
-- Tabling and indexing
-- ---------------------------------------------------------------------------

prop_tabling_left_recursion :: Property
prop_tabling_left_recursion = unit $ do
  let prog =
        unlines
          [ "edge a b.",
            "edge b c.",
            "edge c a.",
            "edge c d.",
            "path X Y <- path X Z, edge Z Y.",
            "path X Y <- edge X Y."
          ]
  sort (run prog "path a X?") === sort ["X = a", "X = b", "X = c", "X = d"]
  assertAnswers prog "path d X?" ["false."]

prop_tabling_memoises :: Property
prop_tabling_memoises = unit $ do
  let prog =
        unlines
          [ "fib 0 0.",
            "fib 1 1.",
            "fib N F <- N > 1, N1 is N - 1, N2 is N - 2, fib N1 F1, fib N2 F2, F is F1 + F2."
          ]
  assertAnswers prog "fib 40 F?" ["F = 102334155"]

prop_tabling_keeps_output :: Property
prop_tabling_keeps_output = unit $ do
  let prog = "count : table (int: <=).\ncount 0 <- write done.\ncount N <- N > 0, N1 is N - 1, count N1."
  assertAnswers prog "count 2?" ["done", "true."]

prop_notable_generator_streams :: Property
prop_notable_generator_streams = unit $ do
  let prog = "gen : notable.\ngen 0.\ngen N <- gen M, N is M + 1."
  assertAnswers prog "gen X, X > 3, !?" ["X = 4"]

prop_indexing_candidates :: Property
prop_indexing_candidates = unit $ do
  prog <- loadOrFail (unlines ["f a 1.", "f b 2.", "f X 3 <- X = c.", "f a 4."])
  p <- predOrFail prog ("f", 2)
  candidateClauses p [Just (IKAtom "a"), Nothing] === [0, 2, 3]
  candidateClauses p [Just (IKAtom "b"), Nothing] === [1, 2]
  candidateClauses p [Nothing, Just (IKInt 3)] === [2]
  candidateClauses p [Nothing, Nothing] === [0, 1, 2, 3]
  -- indexing never changes answers
  let src = unlines ["f a 1.", "f b 2.", "f X 3 <- X = c.", "f a 4."]
  run src "f a N?" === run ("f : noindex (any) (any).\n" ++ src) "f a N?"
  run src "f a N?" === ["N = 1", "N = 4"]

-- ---------------------------------------------------------------------------
-- CLP(Z)
-- ---------------------------------------------------------------------------

prop_clp_basic :: Property
prop_clp_basic = unit $ do
  assertAnswers "" "X #= 3 + 4?" ["X = 7"]
  assertAnswers "" "3 #= X + 1?" ["X = 2"]
  assertAnswers "" "X in 1..3, label [X]?" ["X = 1", "X = 2", "X = 3"]
  assertAnswers "" "X #> 3, X #< 6?" ["X in 4..5"]
  assertAnswers "" "X in 0..5, Y in 0..5, X + Y #= 10?" ["X = 5, Y = 5"]
  assertAnswers "" "X in 1..10, X #!= 5, X #> 3, X #< 7, label [X]?" ["X = 4", "X = 6"]
  assertAnswers "" "X in 1..3, X #= 7?" ["false."]
  assertAnswers "" "X + Y #= 10?" ["X + Y #= 10"]
  assertErrorContains "" "label [X]?" "unbounded domain"
  assertErrorContains "" "X in 1..3, X = a?" "bound to a non-integer"

prop_clp_labeling_solves :: Property
prop_clp_labeling_solves = unit $ do
  assertAnswers "" "[X, Y] in 0..10, X + Y #= 10, X - Y #= 2, label [X, Y]?" ["X = 6, Y = 4"]
  assertAnswers "" "X in 1..2, Y in 1..2, all_different [X, Y], label [X, Y]?" ["X = 1, Y = 2", "X = 2, Y = 1"]
  assertAnswers "" "X in 1..3, Y #= X * 2, label [X]?" ["X = 1, Y = 2", "X = 2, Y = 4", "X = 3, Y = 6"]

prop_clp_queens :: Property
prop_clp_queens = unit $ do
  let prog =
        unlines
          [ "queens N Qs <- mklist N Qs, Qs in 1..N, safe Qs, label Qs.",
            "mklist 0 [].",
            "mklist N [_ | T] <- N > 0, N1 is N - 1, mklist N1 T.",
            "safe [].",
            "safe [Q | Qs] <- noattack Q Qs 1, safe Qs.",
            "noattack _ [] _.",
            "noattack Q [Q1 | Qs] D <- Q #!= Q1, Q #!= Q1 + D, Q #!= Q1 - D, D1 is D + 1, noattack Q Qs D1."
          ]
  assertAnswers prog "queens 4 Qs?" ["Qs = [2, 4, 1, 3]", "Qs = [3, 1, 4, 2]"]
  length (run prog "queens 6 Qs?") === 4

-- ---------------------------------------------------------------------------
-- Modules
-- ---------------------------------------------------------------------------

prop_modules_import_and_qualify :: Property
prop_modules_import_and_qualify = unit $ do
  tmp <- evalIO getTemporaryDirectory
  let modPath = tmp </> "infera_test_mod.nprolog"
      modSrc = unlines ["twice : det (int: <=) (int: =>).", "twice X Y <- Y is X * 2.", "helper 1."]
      conf = Map.fromList [("mymod#abc", modPath)]
  evalIO (writeFile modPath modSrc)
  res <- evalIO (loadSource conf (unlines ["<- import \"mymod#abc\".", "main R <- mymod:twice 21 R.", "> main R?"]))
  case res of
    Left err -> annotate err >> failure
    Right (prog, queries) -> do
      length queries === 1
      map predKey (programPreds prog) === [("mymod:twice", 2), ("mymod:helper", 1), ("main", 1)]
      case queries of
        (q : _) -> map showAnswer (summaryAnswers (solveAll prog q)) === ["R = 42"]
        [] -> failure
      -- declarations travel with the module
      tw <- predOrFail prog ("mymod:twice", 2)
      map sigDet (predDecls tw) === [Det]
  bad <- evalIO (loadSource conf "<- import \"nope#1\".")
  case bad of
    Left err -> assert ("not found" `isInfixOf` err)
    Right _ -> failure

-- ---------------------------------------------------------------------------

inferaGroup :: Group
inferaGroup =
  Group
    "Infera v2"
    [ ("parse atom", prop_parse_atom),
      ("parse int", prop_parse_int),
      ("parse vars numbered", prop_parse_var_is_numbered),
      ("parse lists as cons", prop_parse_list_is_cons),
      ("parse arithmetic", prop_parse_arith),
      ("parse operators", prop_parse_operators),
      ("parse declarations", prop_parse_declaration),
      ("parse hash comments", prop_parse_hash_comment),
      ("parse nocrash", prop_parse_nocrash),
      ("show terms", prop_show_roundtrip),
      ("unify atoms", prop_unify_atoms),
      ("unify var binds", prop_unify_var_binds),
      ("unify occurs check", prop_unify_occurs_check),
      ("unify compound", prop_unify_compound),
      ("unify prefers older var", prop_unify_prefers_older_variable),
      ("engine lists", prop_engine_lists),
      ("engine arithmetic", prop_engine_arith_in_heads),
      ("engine cut", prop_engine_cut),
      ("engine control", prop_engine_control),
      ("engine disequality", prop_engine_disequality),
      ("engine dcg", prop_engine_dcg),
      ("engine output", prop_engine_output),
      ("engine strings", prop_engine_strings),
      ("engine depth limit", prop_engine_depth_limit),
      ("decl modes and sorts", prop_decl_modes_and_sorts),
      ("decl determinism", prop_decl_determinism),
      ("decl multiple modes", prop_decl_multiple_modes),
      ("infer signatures", prop_infer_signatures),
      ("infer guards", prop_infer_guards),
      ("infer commit is sound", prop_infer_commit_is_sound),
      ("infer tabling defaults", prop_infer_tabling_defaults),
      ("tabling left recursion", prop_tabling_left_recursion),
      ("tabling memoises", prop_tabling_memoises),
      ("tabling keeps output", prop_tabling_keeps_output),
      ("notable generator streams", prop_notable_generator_streams),
      ("indexing candidates", prop_indexing_candidates),
      ("clp basic", prop_clp_basic),
      ("clp labeling", prop_clp_labeling_solves),
      ("clp queens", prop_clp_queens),
      ("modules", prop_modules_import_and_qualify)
    ]
