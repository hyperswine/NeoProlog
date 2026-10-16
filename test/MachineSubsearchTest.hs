{-# LANGUAGE OverloadedStrings #-}

-- The native scope driver must preserve the reference resolver's ordered
-- stream, including its deliberately unusual findall variable sharing.
module MachineSubsearchTest (machineSubsearchGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.IntMap.Strict as IM
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import Infera.CLP
import qualified Infera.Engine as Reference
import Infera.Error
import Infera.Infer (inferProgram)
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program
import Infera.Syntax
import Infera.Unify (canonicalize, deepWalk, emptySubst)

data Value
  = VAtom String | VVar VarId | VInt Integer | VFloat Word64
  | VChar Char | VString String | VCompound String [Value]
  deriving (Eq, Show)

value :: Term -> Value
value term = case term of
  Atom a -> VAtom a
  Var v -> VVar v
  IntLit n -> VInt n
  FloatLit n -> VFloat (castDoubleToWord64 n)
  CharLit c -> VChar c
  StrLit s -> VString s
  Compound f args -> VCompound f (map value args)

-- Canonicalize a whole answer, with named roots seeded first, so aliases
-- between distinct bindings cannot disappear during normalization.
canonical :: Query -> [Term] -> [Term]
canonical query terms = case fst (canonicalize emptySubst combined) of
  Compound _ roots -> drop (length names) roots
  _ -> error "canonicalization changed the root constructor"
  where
    names = map (Var . snd) (queryNames query)
    combined = Compound "$scope-observations" (names ++ terms)

canonicalError :: Query -> SolveError -> SolveError
canonicalError query err = case err of
  InstantiationError t -> InstantiationError (norm t)
  ExpectedInteger t -> ExpectedInteger (norm t)
  ExpectedNumber t -> ExpectedNumber (norm t)
  ModeError key i t -> ModeError key i (norm t)
  OutputModeError key i t -> OutputModeError key i (norm t)
  SortError key i sort t -> SortError key i sort (norm t)
  CLPTypeError t -> CLPTypeError (norm t)
  UnboundedDomain t -> UnboundedDomain (norm t)
  TypeError description t -> TypeError description (norm t)
  other -> other
  where
    norm t = case canonical query [t] of
      [result] -> result
      _ -> error "canonicalization changed the number of roots"

data Event
  = Answer [(String, Value)] [String] [Reference.OutputEvent]
  | Exhausted
  | Error SolveError
  | Marker Int
  | Incomplete Value
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
         in Answer (zip (map fst bindings) (map value (canonical query (map snd bindings))))
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
      Reference.BranchExhausted -> Exhausted
      Reference.BranchError err -> Error (canonicalError query err)
      Reference.CutMarker owner -> Marker owner
      Reference.ConsumedIncomplete key -> Incomplete (value (fst (canonicalize emptySubst key)))

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

parse :: String -> PropertyT IO Query
parse source = annotate source >> evalEither (parseQuery source)

compareQuery :: Program -> Query -> PropertyT IO Reference.Search
compareQuery program query = do
  let actual = Machine.solveQuery program query
  observe query actual === observe query (Reference.solveQuery program query)
  pure actual

compareText :: Program -> String -> PropertyT IO (Query, Reference.Search)
compareText program source = do
  query <- parse source
  items <- compareQuery program query
  pure (query, items)

foundStates :: Reference.Search -> [Reference.SolverState]
foundStates items = [state | Reference.Found state <- items]

expectAnswers :: Query -> Reference.Search -> [String] -> PropertyT IO ()
expectAnswers query items expected = do
  [Reference.showAnswer (Reference.projectAnswer query state) | state <- foundStates items] === expected
  [err | Reference.BranchError err <- items] === []
  [() | Reference.BranchExhausted <- items] === []

conj :: Term -> Term -> Term
conj a b = Compound "," [a, b]

alt :: Term -> Term -> Term
alt a b = Compound ";" [a, b]

unify :: Term -> Term -> Term
unify a b = Compound "unify" [a, b]

genScopeGoal :: Int -> Gen Term
genScopeGoal depth = Gen.frequency $
  [(7, leaf)] ++ if depth <= 0 then [] else
    [ (2, conj <$> child <*> child),
      (2, alt <$> child <*> child),
      (2, Compound "call" . (: []) <$> child),
      (2, Compound "once" . (: []) <$> child),
      (2, Compound "not" . (: []) <$> child),
      (2, do c <- child; t <- child; e <- child
             pure (alt (Compound "->" [c, t]) e)),
      (1, do c <- child; t <- child; pure (Compound "->" [c, t])),
      (2, do g <- child; template <- Gen.element [Var 0, Var 1, Compound "pair" [Var 0, Var 1]]
             pure (Compound "findall" [template, g, Var 3])),
      (1, do g <- child; pure (conj (unify (Var 2) g) (Compound "call" [Var 2])))
    ]
  where
    child = genScopeGoal (depth - 1)
    leaf = Gen.choice
      [ Gen.element (map Atom ["true", "fail", "!", "unknown"]),
        Gen.element [Var 2, IntLit 7, StrLit "not callable"],
        Compound "pick" . (: []) <$> Gen.element [Var 0, Var 1, Atom "missing"],
        unify <$> Gen.element [Var 0, Var 1] <*> Gen.element [Var 0, Var 1, IntLit 1, IntLit 2],
        Compound "call" . (: []) <$> Gen.element [Atom "true", Var 2, IntLit 9],
        pure (Compound "call" [Atom "pick", Var 0])
      ]

prop_generated_nested_scopes :: Property
prop_generated_nested_scopes = withTests 300 . property $ do
  goal <- forAll (genScopeGoal 3)
  let program = inferProgram (buildProgram
        [TLClause (Clause (Compound "pick" [IntLit n]) [] 0) | n <- [1, 1, 2]])
      query = Query [goal] [("X", 0), ("Y", 1), ("Goal", 2), ("List", 3)] 4
  _ <- compareQuery program query
  pure ()

prop_first_success_issue_policy :: Property
prop_first_success_issue_policy = unit $ do
  let query goal = Query [goal] [] 0
      bad = Atom "unknown"
      succeeds = alt bad (Atom "true")
      write text = Compound "write" [Atom text]
      cases =
        [ (Compound "not" [succeeds], []),
          (Compound "once" [succeeds], [Error (UnknownPredicate ("unknown", 0)), Answer [] [] []]),
          (alt (Compound "->" [succeeds, write "then"]) (write "else"),
            [Error (UnknownPredicate ("unknown", 0)), Answer [] [] [Reference.WriteEvent "then"]]),
          (alt (Compound "->" [bad, write "then"]) (write "else"),
            [Error (UnknownPredicate ("unknown", 0))]),
          (Compound "not" [alt bad (Atom "fail")], [Error (UnknownPredicate ("unknown", 0))]),
          (alt (Compound "->" [Atom "fail", write "then"]) (write "else"),
            [Answer [] [] [Reference.WriteEvent "else"]])
        ]
  forM_ cases $ \(goal, expected) -> do
    annotateShow goal
    items <- compareQuery emptyProgram (query goal)
    observe (query goal) items === expected
  -- A call's first answer can fail in its caller before a later answer
  -- returns successfully. Subsequent retries must retain both the outer
  -- predicate's success guard and an enclosing scope's buffered issues.
  forM_ [("multi", "many"), ("det", "one")] $ \(determinism, name) ->
    forM_ [False, True] $ \hasError -> do
      let picked = if hasError then "(unknown ; pick X)" else "(pick X)"
          errors = [Error (UnknownPredicate ("unknown", 0)) | hasError]
          acceptedAnswer = Answer [("X", VInt 2)] [] []
          list xs = Answer [("L", value (mkList xs Nothing))] [] []
      program <- load $ unlines
        [ "pick 1.", "pick 2.", name ++ " : " ++ determinism ++ " (int: =>).",
          name ++ " X <- call " ++ picked ++ ", X = 2."
        ]
      forM_
        [ (name ++ " X?", errors ++ [acceptedAnswer]),
          (name ++ " X, fail?", errors),
          ("once (" ++ name ++ " X)?", errors ++ [acceptedAnswer]),
          ("not (" ++ name ++ " X)?", []),
          ("not (" ++ name ++ " X, fail)?", if hasError then errors else [Answer [] [] []]),
          ("(" ++ name ++ " X -> true ; X = otherwise)?", errors ++ [acceptedAnswer]),
          ("((" ++ name ++ " X, fail) -> true ; X = otherwise)?",
            if hasError then errors else [Answer [("X", VAtom "otherwise")] [] []]),
          ("findall X (" ++ name ++ " X) L?", if hasError then errors else [list [IntLit 2]]),
          ("findall X (" ++ name ++ " X, fail) L?", if hasError then errors else [list []])
        ] $ \(source, expected) -> do
          (scopedQuery, scopedItems) <- compareText program source
          observe scopedQuery scopedItems === expected

prop_fuel_and_error_policy :: Property
prop_fuel_and_error_policy = unit $ do
  program <- load "step : notable.\nstep X."
  let env = Reference.mkEnv program
      query = Query [] [("X", 0), ("List", 1)] 2
      state = Reference.initialState 2
      exhausted = Compound "step" [Var 0]
      bad = Atom "unknown"
      answer = unify (Var 0) (IntLit 7)
      run goal = do
        annotateShow goal
        let actual = Machine.solveGoals env 0 state [goal]
        observe query actual === observe query (Reference.solveGoals env 0 state [goal])
        pure actual
  negated <- run (Compound "not" [alt exhausted answer])
  observe query negated === []
  onceItems <- run (Compound "once" [alt exhausted answer])
  observe query onceItems ===
    [Exhausted, Answer [("X", VInt 7)] [] []]
  committed <- run (alt (Compound "->" [alt exhausted answer, Atom "true"]) (Atom "fail"))
  observe query committed ===
    [Exhausted, Answer [("X", VInt 7)] [] []]
  conditional <- run (alt (Compound "->" [exhausted, Atom "true"]) (unify (Var 0) (Atom "else")))
  observe query conditional === [Exhausted]
  negatedExhaustion <- run (Compound "not" [exhausted])
  observe query negatedExhaustion === [Exhausted]
  collected <- run (Compound "findall" [Var 0, alt exhausted answer, Var 1])
  observe query collected ===
    [Exhausted, Answer [("List", VCompound "cons" [VInt 7, VAtom "nil"])] [] []]
  errored <- run (Compound "findall"
    [Var 0, alt answer (alt exhausted (alt bad (Atom "another_unknown"))), Var 1])
  -- findall discards collected solutions and exhaustion on errors, returns
  -- only the first error, and never invokes the caller's continuation.
  observe query errored === [Error (UnknownPredicate ("unknown", 0))]
  -- Mutual recursion exercises real incomplete-table dependencies internally.
  -- Public root evaluation absorbs those ancestor signals before returning;
  -- constructing a private TableEntry merely to force them out would change
  -- the production API for the sake of a test.
  mutual <- load "p X <- q X.\nq X <- p X.\nq seed."
  forM_
    [ ("call (p X)?", ["X = seed"]),
      ("once (p X)?", ["X = seed"]),
      ("not (p X)?", []),
      ("(p X -> X = seed ; X = otherwise)?", ["X = seed"]),
      ("findall X (call (p X)) L?", ["L = [seed]"])
    ] $ \(text, expected) -> do
      (mutualQuery, mutualItems) <- compareText mutual text
      expectAnswers mutualQuery mutualItems expected

prop_call_shape_and_types :: Property
prop_call_shape_and_types = unit $ do
  program <- load "pair a b.\npick 1.\npick 2."
  forM_
    [ ("call pair a X?", ["X = b"]),
      ("P = (pair a), call P X?", ["P = pair a, X = b"]),
      ("call (pair X) b?", ["X = a"]),
      ("G = (H ; X = otherwise), H = (true -> X = then), call G?", [])
    ] $ \(text, expected) -> do
      (query, items) <- compareText program text
      if null expected then length (foundStates items) === 2 else expectAnswers query items expected
  forM_ [Atom "true", Atom "fail", Var 0, IntLit 7, StrLit "bad"] $ \target -> do
    let query = Query [Compound "call" [target]] [("G", 0)] 1
        err = case target of
          Atom name -> UnknownPredicate (name, 0)
          other -> TypeError "callable" other
    items <- compareQuery emptyProgram query
    observe query items === [Error err]

prop_nested_cut_boundaries :: Property
prop_nested_cut_boundaries = unit $ do
  program <- load $ unlines
    ["pick 1.", "pick 2.", "local : nondet unsafe (any: <=>).",
     "local X <- pick X, !.", "local fallback."]
  forM_
    [ ("(call (pick X, !, fail) ; X = fallback)?", ["X = fallback"]),
      ("(once (pick X, !, fail) ; X = fallback)?", ["X = fallback"]),
      ("call (pick X, !), pick Y?", ["X = 1, Y = 1", "X = 1, Y = 2"]),
      ("once (call (pick X, !)), pick Y?", ["X = 1, Y = 1", "X = 1, Y = 2"]),
      ("findall X (pick X, !) L, pick Y?", ["L = [1], Y = 1", "L = [1], Y = 2"]),
      ("((pick X, !) -> pick Y ; X = otherwise)?", ["X = 1, Y = 1", "X = 1, Y = 2"]),
      ("findall X (once (local X)) L, local Y?", ["L = [1], Y = 1"])
    ] $ \(text, expected) -> do
      (query, items) <- compareText program text
      expectAnswers query items expected

prop_findall_identity_and_fresh_reuse :: Property
prop_findall_identity_and_fresh_reuse = unit $ do
  program <- load "local (pair A A)."
  forM_
    [ ("findall X true L, X = shared?", ["X = shared, L = [shared]"]),
      ("X = (box Y), findall X true L, Y = shared?", ["X = box shared, Y = shared, L = [box shared]"]),
      ("findall X fail L?", ["L = []"]),
      ("findall X (local X) L, local Y, Y = (pair linked linked)?",
        ["L = [pair linked linked], Y = pair linked linked"])
    ] $ \(text, expected) -> do
      (query, items) <- compareText program text
      expectAnswers query items expected
      if "local" `isInfixOf` text
        then map Reference.ssFresh (foundStates items) === [queryNVars query + 1]
        else pure ()
  (query, items) <- compareText emptyProgram
    "findall (pair X Y) (Y = X ; true) L, X = shared?"
  let expected = mkList
        [Compound "pair" [Atom "shared", Atom "shared"], Compound "pair" [Atom "shared", Var 1]] Nothing
  case foundStates items of
    [state] -> do
      let listId = maybe (error "missing List root") id (lookup "L" (queryNames query))
      deepWalk (stSubst (Reference.ssStore state)) (Var listId) === expected
      Reference.ssFresh state === queryNVars query
    _ -> failure

-- Store representation may contain different substitution paths after heap
-- export. All other state fields must still agree exactly at scope exits.
compareState :: Reference.SolverState -> Reference.SolverState -> PropertyT IO ()
compareState actual expected = do
  Reference.ssFresh actual === Reference.ssFresh expected
  Reference.ssOutLen actual === Reference.ssOutLen expected
  Reference.ssOutput actual === Reference.ssOutput expected
  Reference.ssDynamic actual === Reference.ssDynamic expected
  show (Reference.ssTables actual) === show (Reference.ssTables expected)
  (Reference.ssStore actual) {stSubst = emptySubst} === (Reference.ssStore expected) {stSubst = emptySubst}

prop_full_scope_state_retention :: Property
prop_full_scope_state_retention = unit $ do
  program <- load "fact : dynamic.\ndep X <- dep X.\ndep a."
  forM_
    [ ("not (assert (fact child), X in 1..3, dep T, write child, fail)?", False, []),
      ("findall X (assert (fact child), X in 1..3, dep T, write child) L?", False, [Reference.WriteEvent "child"]),
      ("once (assert (fact child), X in 1..3, dep T, write child)?", True, [Reference.WriteEvent "child"]),
      ("call (assert (fact child), X in 1..3, dep T, write child)?", True, [Reference.WriteEvent "child"]),
      ("((assert (fact child), X in 1..3, dep T, write child) -> true ; fail)?", True, [Reference.WriteEvent "child"])
    ] $ \(text, retained, output) -> do
      (query, items) <- compareText program text
      let reference = foundStates (Reference.solveQuery program query)
      length (foundStates items) === 1
      forM_ (zip (foundStates items) reference) $ \(actual, expected) -> do
        compareState actual expected
        reverse (Reference.ssOutput actual) === output
        Map.null (Reference.ssDynamic actual) === not retained
        Map.null (Reference.ssTables actual) === not retained
        IM.null (stDomains (Reference.ssStore actual)) === not retained

prop_findall_output_and_error_rollback :: Property
prop_findall_output_and_error_rollback = unit $ do
  program <- load "pick 1.\npick 1.\npick 2."
  (query, items) <- compareText program
    "write before, findall X (pick X, write X, nl) L, write after?"
  expectAnswers query items ["L = [1, 1, 2]"]
  case foundStates items of
    [state] -> reverse (Reference.ssOutput state) ===
      [Reference.WriteEvent "before", Reference.WriteEvent "1", Reference.NewlineEvent,
       Reference.WriteEvent "1", Reference.NewlineEvent, Reference.WriteEvent "2",
       Reference.NewlineEvent, Reference.WriteEvent "after"]
    _ -> failure
  (errorQuery, errorItems) <- compareText emptyProgram
    "write before, (findall X (write child, (X = 1 ; unknown ; X = 2)) L ; true)?"
  observe errorQuery errorItems ===
    [Error (UnknownPredicate ("unknown", 0)), Answer [] [] [Reference.WriteEvent "before"]]

drain :: Machine.Checkpoint -> Either Heap.HeapError Reference.Search
drain state = do
  step <- Machine.resume state
  case step of
    Machine.Finished -> pure []
    Machine.Yield item next -> (item :) <$> drain next

prefix :: Int -> Machine.Checkpoint -> Either Heap.HeapError Reference.Search
prefix count _ | count <= 0 = pure []
prefix count state = do
  step <- Machine.resume state
  case step of
    Machine.Finished -> pure []
    Machine.Yield item next -> (item :) <$> prefix (count - 1) next

prop_scope_resume_immutability_and_laziness :: Property
prop_scope_resume_immutability_and_laziness = unit $ do
  program <- load "pick (pair A A).\npick first.\npick second."
  query <- parse "call (pick X), findall (pair X Y) (pick Y, write Y) L, (once (pick Z) ; not fail)?"
  initial <- evalEither (Machine.start program query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = observe query [retained]
      _ <- evalIO (evaluate (length (show before)))
      suffix <- evalEither (drain next)
      complete <- evalEither (drain initial)
      repeated <- evalEither (drain next)
      observe query complete === observe query (Reference.solveQuery program query)
      observe query suffix === observe query repeated
      observe query (retained : suffix) === observe query complete
      observe query [retained] === before
  lazyProgram <- load "p : nondet notable (any: <=>).\np first.\np X <- p X."
  forM_ ["call (p X)?", "once (call (p X))?", "(call (p X) -> X = first ; fail)?", "not (call (p X))?"] $ \text -> do
    lazyQuery <- parse text
    initialLazy <- evalEither (Machine.start lazyProgram lazyQuery)
    firstPrefix <- evalEither (prefix 3 initialLazy)
    secondPrefix <- evalEither (prefix 3 initialLazy)
    observe lazyQuery firstPrefix === observe lazyQuery (take 3 (Reference.solveQuery lazyProgram lazyQuery))
    observe lazyQuery secondPrefix === observe lazyQuery firstPrefix

machineSubsearchGroup :: Group
machineSubsearchGroup = Group "machine native sub-search"
  [ ("generated_nested_scopes", prop_generated_nested_scopes),
    ("first_success_issue_policy", prop_first_success_issue_policy),
    ("fuel_and_error_policy", prop_fuel_and_error_policy),
    ("call_shape_and_types", prop_call_shape_and_types),
    ("nested_cut_boundaries", prop_nested_cut_boundaries),
    ("findall_identity_and_fresh_reuse", prop_findall_identity_and_fresh_reuse),
    ("full_scope_state_retention", prop_full_scope_state_retention),
    ("findall_output_and_error_rollback", prop_findall_output_and_error_rollback),
    ("scope_resume_immutability_and_laziness", prop_scope_resume_immutability_and_laziness)
  ]
