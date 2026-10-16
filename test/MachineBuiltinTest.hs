{-# LANGUAGE OverloadedStrings #-}

-- Finite builtin iterators never recursively call the reference resolver.
-- Test their full persistent transactions independently, then exercise those
-- transactions with native choices, CLP wakeups and opaque scopes.
module MachineBuiltinTest (machineBuiltinGroup) where

import Control.Monad (forM_)
import qualified Data.Map.Strict as Map
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP (Store, stSubst)
import qualified Infera.Engine.Reference as Reference
import Infera.Error (PredKey, SolveError)
import qualified Infera.Machine.Builtins as Builtins
import qualified Infera.Machine.Control as Machine
import Infera.Program (Program, addFiles, buildProgram)
import Infera.Syntax
import Infera.Unify (canonicalize, deepWalk, emptySubst)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

emptyProgram :: Program
emptyProgram = buildProgram []

data RawEvent
  = RawFound Store Int [Reference.OutputEvent] Int (Map.Map PredKey [(Term, Int)])
  | RawError SolveError | RawExhausted | RawCut Int | RawIncomplete Term
  deriving (Eq, Show)

rawEvents :: Reference.Search -> [RawEvent]
rawEvents = map event
  where
    event item = case item of
      Reference.Found state -> RawFound (Reference.ssStore state) (Reference.ssFresh state)
        (Reference.ssOutput state) (Reference.ssOutLen state) (Reference.ssDynamic state)
      Reference.BranchError err -> RawError err
      Reference.BranchExhausted -> RawExhausted
      Reference.CutMarker owner -> RawCut owner
      Reference.ConsumedIncomplete key -> RawIncomplete key

compareBuiltin :: Reference.Env -> Reference.SolverState -> Term -> PropertyT IO ()
compareBuiltin environment state goal = do
  annotateShow goal
  actual <- maybe (annotate "builtin was not handled" >> failure) pure
    (Builtins.ordinaryBuiltin environment state goal)
  rawEvents actual === rawEvents (Reference.solveGoal environment 0 state goal)

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent] (Map.Map PredKey [(Term, Int)])
  | Error String | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
            roots = Compound "$builtin_roots" (map (Var . snd) (queryNames query) ++ map snd bindings)
            canonical = case fst (canonicalize emptySubst roots) of
              Compound _ values -> drop (length (queryNames query)) values
              _ -> error "canonicalization changed a compound"
         in Answer (zip (map fst bindings) canonical) (Reference.answerResiduals answer)
              (Reference.answerOutput answer) (Reference.ssDynamic state)
      Reference.BranchError err -> Error (show err)
      Reference.BranchExhausted -> Exhausted
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete key

compareQuery :: Program -> Query -> PropertyT IO Reference.Search
compareQuery program query = do
  let actual = Machine.solveQuery program query
  observe query actual === observe query (Reference.solveQuery program query)
  pure actual

compareText :: Program -> String -> PropertyT IO Reference.Search
compareText program source = do
  annotate source
  query <- evalEither (parseQuery source)
  compareQuery program query

list :: [Term] -> Term
list terms = mkList terms Nothing

prop_generated_string_transactions :: Property
prop_generated_string_transactions = withTests 400 . property $ do
  text <- forAll (Gen.string (Range.linear 0 8) (Gen.element ['a', 'B', ' ', '\n', '\x1f642']))
  prefix <- forAll (Gen.string (Range.linear 0 4) (Gen.element ['x', '\x03bb']))
  let environment = Reference.mkEnv emptyProgram
      state = Reference.initialState 4
      cases =
        [ Compound "str_concat" [Var 0, Var 1, StrLit text],
          Compound "str_concat" [StrLit prefix, StrLit text, Var 0],
          Compound "str_concat" [Var 0, Var 0, StrLit text],
          Compound "str_chars" [StrLit text, Var 0],
          Compound "str_chars" [Var 0, list (map CharLit text)],
          Compound "str_length" [StrLit text, Var 0],
          Compound "str_upper" [StrLit text, Var 0],
          Compound "str_lower" [StrLit text, Var 0],
          Compound "str_lines" [StrLit text, Var 0],
          Compound "str_atom" [StrLit text, Var 0],
          Compound "str_atom" [Var 0, Atom text],
          Compound "term_str" [Compound "pair" [StrLit text, Compound "plus" [IntLit 2, IntLit 3]], Var 0]
        ]
  forM_ cases (compareBuiltin environment state)

prop_generated_split_answers_independent_model :: Property
prop_generated_split_answers_independent_model = withTests 300 . property $ do
  text <- forAll (Gen.string (Range.linear 0 12) (Gen.element ['a', 'b', '\x03bb']))
  let query = Query [Compound "str_concat" [Var 0, Var 1, StrLit text]] [("Left", 0), ("Right", 1)] 2
  actual <- compareQuery emptyProgram query
  [ [deepWalk (stSubst (Reference.ssStore state)) (Var variable) | variable <- [0, 1]]
    | Reference.Found state <- actual ] ===
      [[StrLit prefix, StrLit suffix] | index <- [0 .. length text], let (prefix, suffix) = splitAt index text]

prop_generated_dcg_prefixes :: Property
prop_generated_dcg_prefixes = withTests 200 . property $ do
  characters <- forAll (Gen.list (Range.linear 0 9) (CharLit <$> Gen.element ['a', 'b', '\x03bb']))
  let environment = Reference.mkEnv emptyProgram
      state = Reference.initialState 2
      goal = Compound "seq" [Var 0, list characters, Var 1]
      query = Query [goal] [("Prefix", 0), ("Rest", 1)] 2
  compareBuiltin environment state goal
  actual <- compareQuery emptyProgram query
  [ [deepWalk (stSubst (Reference.ssStore accepted)) (Var variable) | variable <- [0, 1]]
    | Reference.Found accepted <- actual ] ===
      [[list prefix, list suffix] | index <- [0 .. length characters], let (prefix, suffix) = splitAt index characters]

prop_builtin_errors_and_shallow_inputs :: Property
prop_builtin_errors_and_shallow_inputs = unit $ do
  let environment = Reference.mkEnv emptyProgram
      state = Reference.initialState 4
  forM_
    [ Compound "str_concat" [Var 0, Var 1, Var 2],
      Compound "str_length" [Var 0, Var 1],
      Compound "str_chars" [Var 0, list [Var 1]],
      Compound "str_chars" [Var 0, mkList [CharLit 'a'] (Just (Var 1))],
      Compound "str_chars" [IntLit 1, Var 0],
      Compound "str_atom" [Var 0, Var 1],
      Compound "str_num" [StrLit "not a number", Var 0],
      Compound "str_num" [Var 0, Var 1],
      Compound "str_upper" [Atom "hello", Var 0],
      Compound "str_lines" [IntLit 1, Var 0],
      Compound "char_code" [Var 0, Var 1],
      Compound "seq" [Var 0, Var 1, Var 2],
      Compound "padl" [Atom "value", Var 0, Var 1, Var 2],
      Compound "fmt" [StrLit "~d", list [Atom "bad"], Var 0, Atom "nil"],
      Compound "fmt" [StrLit "~w", Atom "nil", Var 0, Atom "nil"],
      Compound "fmt" [StrLit "~z", Atom "nil", Var 0, Atom "nil"],
      Compound "fmt" [StrLit "text", list [IntLit 1], Var 0, Atom "nil"],
      Compound "fmt" [Var 0, Atom "nil", Var 1, Atom "nil"]
    ] (compareBuiltin environment state)
  forM_
    [ "X = [a | Tail], is_list X?",
      "X = [a], is_list X, ground X, nonvar X, not (var X)?",
      "X = 2 + 3, term_str X Text, write X, print Text, writeln done, nl?",
      "G = str_length Text N, Text = \"hello\", call G?",
      "X in 1..3, str_length \"ab\" X, label [X]?",
      "X in 1..3, (str_chars X C ; X = 2), label [X]?"
    ] $ \source -> compareText emptyProgram source >> pure ()

prop_type_and_number_conversions :: Property
prop_type_and_number_conversions = unit $ do
  let environment = Reference.mkEnv emptyProgram
      state = Reference.initialState 3
  forM_ ["var", "nonvar", "ground", "is_int", "is_float", "is_num", "is_str", "is_atom", "is_char", "is_list"] $ \name ->
    forM_ [Var 0, Atom "word", IntLit 2, FloatLit 2.5, StrLit "text", CharLit '\x03bb', list [IntLit 1], Compound "pair" [Var 1, Atom "nil"]] $ \term ->
      compareBuiltin environment state (Compound name [term])
  forM_
    [ Compound "str_num" [StrLit "12", Var 0],
      Compound "str_num" [StrLit "-2.5", Var 0],
      Compound "str_num" [Var 0, IntLit (10 ^ (70 :: Int))],
      Compound "str_num" [Var 0, FloatLit 2.5],
      Compound "char_code" [CharLit '\x1f642', Var 0],
      Compound "char_code" [Var 0, IntLit 955]
    ] (compareBuiltin environment state)

prop_output_dcg_and_backtracking :: Property
prop_output_dcg_and_backtracking = unit $ do
  program <- evalEither . Reference.loadProgramText $ unlines
    [ "render : unsafe.",
      "render -> wr (1 + 2), sp, padl abc 5, sp, padr xyz 5, nl, fmt \"~a:~d:~s:~~:~n\" [name, 4, \"ok\"].",
      "effect : unsafe.",
      "effect X <- (write discarded, X = bad, fail ; writeln kept, X = good)."
    ]
  forM_
    [ "emit render?",
      "phrase render Text?",
      "effect X?",
      "findall (pair A B) (str_concat A B \"abc\", write A) Answers?",
      "once (str_concat A B \"abc\"), write B?",
      "not (str_concat A B \"abc\", write A, fail), write kept?",
      "(str_concat A B \"abc\", A = \"a\" -> write B ; write missing)?",
      "phrase (seq Prefix) [a, b], write Prefix?"
    ] $ \source -> compareText program source >> pure ()

prop_preloaded_file_behavior :: Property
prop_preloaded_file_behavior = unit $ do
  let program = addFiles [("fixture.txt", "a\nb\n")] emptyProgram
      environment = Reference.mkEnv program
      state = Reference.initialState 3
  forM_
    [ Compound "read_file" [StrLit "fixture.txt", Var 0],
      Compound "read_file" [StrLit "fixture.txt", StrLit "wrong"],
      Compound "read_file" [StrLit "missing.txt", Var 0],
      Compound "read_file" [Var 0, Var 1],
      Compound "read_file" [Atom "fixture.txt", Var 0]
    ] (compareBuiltin environment state)
  _ <- compareText program "read_file \"fixture.txt\" Text, str_lines Text Lines?"
  pure ()

prop_dynamic_facts_choices_freshness_and_rollback :: Property
prop_dynamic_facts_choices_freshness_and_rollback = unit $ do
  program <- evalEither . Reference.loadProgramText $ unlines
    [ "memo : dynamic.",
      "other : dynamic.",
      "effect : unsafe.",
      "effect X <- assert (memo kept), memo X."
    ]
  forM_
    [ "assert (memo first), assert (memo second), memo X?",
      "assert (memo first), assert (memo second), retract (memo X), memo Y?",
      "assert (memo first), assert (memo second), retractall (memo first), memo X?",
      "assert (memo (pair X X)), memo (pair A B), A = done, memo (pair C D), C = next?",
      "(assert (memo discarded), fail ; memo X)?",
      "(assert (memo first), memo X ; assert (memo second), memo X)?",
      "assert (memo first), once (retract (memo X)), not (memo Y)?",
      "assert (memo first), findall X (retract (memo X)) Removed, memo Remaining?",
      "assert (memo first), assert (memo second), findall X (memo X) Answers?",
      "assert (memo first), not (retract (memo X), fail), memo Remaining?",
      "assert (memo first), (retract (memo X) -> memo Remaining ; true)?",
      "effect X?",
      "assert (unknown value)?",
      "assert 1?",
      "retract 1?",
      "retractall 1?"
    ] $ \source -> compareText program source >> pure ()

machineBuiltinGroup :: Group
machineBuiltinGroup = Group "machine ordinary builtins"
  [ ("generated_string_transactions", prop_generated_string_transactions),
    ("generated_split_answers_independent_model", prop_generated_split_answers_independent_model),
    ("generated_dcg_prefixes", prop_generated_dcg_prefixes),
    ("builtin_errors_and_shallow_inputs", prop_builtin_errors_and_shallow_inputs),
    ("type_and_number_conversions", prop_type_and_number_conversions),
    ("output_dcg_and_backtracking", prop_output_dcg_and_backtracking),
    ("preloaded_file_behavior", prop_preloaded_file_behavior),
    ("dynamic_facts_choices_freshness_and_rollback", prop_dynamic_facts_choices_freshness_and_rollback)
  ]
