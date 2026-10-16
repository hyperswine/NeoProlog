{-# LANGUAGE OverloadedStrings #-}

-- Closed trees have an independent ordered-answer model; open trees exercise
-- the language's existing cut, opaque-search, error and raw-syntax semantics
-- against both older engines. Counters prove that their root control executes
-- as compiled instructions rather than only compiling leaf predicates.
module MachineCompiledControlTest (machineCompiledControlGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_, when)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP
import Infera.Compile (compileClause)
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program (Program, addClause)
import Infera.Syntax
import qualified Infera.Unify as Unify

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText source = annotate source >> evalEither (parseQuery source)

bits :: Term -> Term
bits (FloatLit number) = Compound "$compiled_control_float_bits"
  [IntLit (fromIntegral (castDoubleToWord64 number))]
bits (Compound name arguments) = Compound name (map bits arguments)
bits term = term

storeBits :: Store -> Store
storeBits store = store
  { stSubst = IM.map bits (stSubst store),
    stConstraints = map constraintBits (stConstraints store),
    stConstraintMap = IM.map constraintBits (stConstraintMap store)
  }
  where
    constraintBits (CNonLinear relation left right) = CNonLinear relation (bits left) (bits right)
    constraintBits (CDiseq left right) = CDiseq (bits left) (bits right)
    constraintBits (CAllDifferent terms) = CAllDifferent (map bits terms)
    constraintBits (CReified relation left right truth) = CReified relation (bits left) (bits right) (bits truth)
    constraintBits other = other

errorTerms :: (Term -> Term) -> SolveError -> SolveError
errorTerms transform problem = case problem of
  InstantiationError term -> InstantiationError (transform term)
  ExpectedInteger term -> ExpectedInteger (transform term)
  ExpectedNumber term -> ExpectedNumber (transform term)
  ModeError key index term -> ModeError key index (transform term)
  OutputModeError key index term -> OutputModeError key index (transform term)
  SortError key index sort' term -> SortError key index sort' (transform term)
  CLPTypeError term -> CLPTypeError (transform term)
  UnboundedDomain term -> UnboundedDomain (transform term)
  TypeError description term -> TypeError description (transform term)
  other -> other

canonical :: Query -> [Term] -> [Term]
canonical query terms = case fst (Unify.canonicalize Unify.emptySubst combined) of
  Compound _ roots -> map bits (drop (length names) roots)
  _ -> error "canonicalization changed compound shape"
  where
    names = map (Var . snd) (queryNames query)
    combined = Compound "$compiled_control_roots" (names ++ terms)

type TableMetadata = Map.Map Term
  (Bool, Bool, [(Term, Int, [Reference.OutputEvent])], Set.Set Term)

tableMetadata :: Reference.SolverState -> TableMetadata
tableMetadata = Map.mapKeys bits . Map.map entry . Reference.ssTables
  where
    entry table = (Reference.teComplete table, Reference.teTruncated table,
      [(bits term, count, output) | (term, count, output) <- Reference.teAnswers table],
      Set.map bits (Reference.teSet table))

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent] Store Int Int
      TableMetadata (Map.Map PredKey [(Term, Int)])
  | Error SolveError | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

events :: Query -> Reference.Search -> [Event]
events query = map event
  where
    normalize term = case canonical query [term] of
      [value] -> value
      _ -> error "canonicalization changed root count"
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
            metadata = storeBits ((Reference.ssStore state) {stSubst = Unify.emptySubst})
            dynamic = Map.map (map (\(term, count) -> (bits term, count))) (Reference.ssDynamic state)
         in Answer (zip (map fst bindings) (canonical query (map snd bindings)))
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
              metadata (Reference.ssFresh state) (Reference.ssOutLen state)
              (tableMetadata state) dynamic
      Reference.BranchError problem -> Error (errorTerms normalize problem)
      Reference.BranchExhausted -> Exhausted
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete (bits (fst (Unify.canonicalize Unify.emptySubst key)))

drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Metrics)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], Machine.checkpointMetrics checkpoint)
    Machine.Yield item next -> do
      (remaining, metrics) <- drain next
      pure (item : remaining, metrics)

compareQuery :: Program -> Query -> PropertyT IO Reference.Search
compareQuery program query = do
  let actual = Machine.solveQueryWithBackend Machine.Bytecode program query
      interpreted = Machine.solveQueryWithBackend Machine.Interpreted program query
      reference = Reference.solveQuery program query
  events query actual === events query interpreted
  events query actual === events query reference
  pure actual

rawStores :: Reference.Search -> [Store]
rawStores items = [storeBits (Reference.ssStore state) | Reference.Found state <- items]

drainTraced :: Machine.Checkpoint -> Either Heap.HeapError ([Trace.TraceEvent], Reference.Search)
drainTraced checkpoint = do
  (trace, step) <- Machine.resumeTraced checkpoint
  case step of
    Machine.Finished -> pure (trace, [])
    Machine.Yield item next -> do
      (laterTrace, later) <- drainTraced next
      pure (trace ++ laterTrace, item : later)

traceBits :: [Trace.TraceEvent] -> [Trace.TraceEvent]
traceBits = map (\event -> event {Trace.traceGoal = bits (Trace.traceGoal event),
  Trace.traceError = errorTerms bits <$> Trace.traceError event})

assertTraceParity :: Program -> Query -> PropertyT IO ()
assertTraceParity program query = do
  compiled <- evalEither (Machine.startTracedWithBackend Machine.Bytecode program query)
  interpreted <- evalEither (Machine.startTracedWithBackend Machine.Interpreted program query)
  (trace, actual) <- evalEither (drainTraced compiled)
  (oldTrace, expected) <- evalEither (drainTraced interpreted)
  traceBits trace === traceBits oldTrace
  events query actual === events query expected
  events query actual === events query (Reference.solveQuery program query)
  (replayedTrace, replayed) <- evalEither (drainTraced compiled)
  traceBits replayedTrace === traceBits trace
  events query replayed === events query actual

assertFuelParity :: Program -> Query -> [Int] -> PropertyT IO ()
assertFuelParity program query budgets = forM_ budgets $ \fuel -> do
  annotateShow fuel
  let environment = Reference.mkEnv program
      state = Reference.initialState (queryNVars query)
      expected = Reference.solveGoals environment fuel state (queryGoals query)
  forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
    initial <- evalEither (Machine.startGoalsWithBackend backend environment fuel state (queryGoals query))
    (actual, _) <- evalEither (drain initial)
    events query actual === events query expected
    rawStores actual === rawStores expected

data Closed
  = Value Term | Empty | Both Closed Closed | Choice Closed Closed
  | Invoke Closed | First Closed | Absent Closed
  | Conditional Closed Closed Closed | Collect Closed
  deriving Show

model :: Closed -> [Term]
model tree = case tree of
  Value value -> [value]
  Empty -> []
  Both left right -> [Compound "pair" [a, b] | a <- model left, b <- model right]
  Choice left right -> model left ++ model right
  Invoke child -> model child
  First child -> take 1 (model child)
  Absent child -> [Atom "absent" | null (model child)]
  Conditional condition yes no -> model (if null (model condition) then no else yes)
  Collect child -> [mkList (model child) Nothing]

genClosed :: Int -> Gen Closed
genClosed depth = Gen.frequency $
  [(4, Value <$> scalar), (1, pure Empty)] ++ if depth <= 0 then [] else
    [ (2, Both <$> child <*> child), (3, Choice <$> child <*> child),
      (1, Invoke <$> child), (2, First <$> child), (1, Absent <$> child),
      (2, Conditional <$> child <*> child <*> child), (2, Collect <$> child)
    ]
  where
    child = genClosed (depth - 1)
    scalar = Gen.choice
      [ Atom <$> Gen.element ["a", "same", "\955"],
        IntLit <$> Gen.integral (Range.linear (-2) 2),
        FloatLit <$> Gen.element [-0.0, 0.0, 1.5, castWord64ToDouble 0x7ff8000000000042],
        CharLit <$> Gen.element ['a', '\955'], StrLit <$> Gen.element ["", "same", "\955"]
      ]

unify :: Term -> Term -> Term
unify left right = Compound "unify" [left, right]

conjoin :: Term -> Term -> Term
conjoin left right = Compound "," [left, right]

-- Each conjunction receives separate result locals, making its product model
-- independent of language unification. Branches share only the target result.
lower :: Closed -> VarId -> VarId -> (Term, VarId)
lower tree output fresh = case tree of
  Value value -> (unify (Var output) value, fresh)
  Empty -> (Atom "fail", fresh)
  Both left right ->
    let a = fresh
        b = fresh + 1
        (leftGoal, afterLeft) = lower left a (fresh + 2)
        (rightGoal, afterRight) = lower right b afterLeft
     in (conjoin leftGoal (conjoin rightGoal
          (unify (Var output) (Compound "pair" [Var a, Var b]))), afterRight)
  Choice left right ->
    let (leftGoal, afterLeft) = lower left output fresh
        (rightGoal, afterRight) = lower right output afterLeft
     in (Compound ";" [leftGoal, rightGoal], afterRight)
  Invoke child ->
    let (goal, after) = lower child output fresh
        -- `call fail` has the current language's Compound fail [] behavior.
        -- A literal conjunction keeps this closed model focused on search.
     in (Compound "call" [conjoin (Atom "true") goal], after)
  First child -> let (goal, after) = lower child output fresh
     in (Compound "once" [goal], after)
  Absent child ->
    let (goal, after) = lower child fresh (fresh + 1)
     in (conjoin (Compound "not" [goal]) (unify (Var output) (Atom "absent")), after)
  Conditional condition yes no ->
    let (conditionGoal, afterCondition) = lower condition fresh (fresh + 1)
        (yesGoal, afterYes) = lower yes output afterCondition
        (noGoal, afterNo) = lower no output afterYes
     in (Compound ";" [Compound "->" [conditionGoal, yesGoal], noGoal], afterNo)
  Collect child ->
    let (goal, after) = lower child fresh (fresh + 1)
     in (Compound "findall" [Var fresh, goal, Var output], after)

assertCompiledControl :: Machine.Metrics -> PropertyT IO ()
assertCompiledControl metrics = do
  annotateShow metrics
  assert (Machine.metricCompiledActivations metrics > 0)
  assert (Machine.metricCompiledControlInstructions metrics > 0)

prop_closed_control_trees_match_independent_model :: Property
prop_closed_control_trees_match_independent_model = withTests 300 . property $ do
  tree <- forAll (genClosed 3)
  let (goal, variables) = lower tree 0 1
      clause = Clause (Compound "root" [Var 0]) [conjoin (Atom "true") goal] variables
      query = Query [Compound ";" [Compound "root" [Var 0], unify (Var 0) (Atom "fallback")]] [("Result", 0)] 1
  _ <- evalMaybe (compileClause clause)
  base <- load "<- notable.\nroot : nondet unsafe (any: <=>)."
  let program = addClause clause base
      expectedValues = map bits (model tree ++ [Atom "fallback"])
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, metrics) <- evalEither (drain initial)
  let interpreted = Machine.solveQueryWithBackend Machine.Interpreted program query
      reference = Reference.solveQuery program query
  events query actual === events query interpreted
  events query actual === events query reference
  rawStores actual === rawStores interpreted
  rawStores actual === rawStores reference
  [bits value | Reference.Found state <- actual,
    Just value <- [lookup "Result" (Reference.answerBindings (Reference.projectAnswer query state))]] === expectedValues
  [problem | Reference.BranchError problem <- actual] === []
  [() | Reference.BranchExhausted <- actual] === []
  assertCompiledControl metrics

genOpen :: Int -> Gen Term
genOpen depth = Gen.frequency $
  [(6, leaf)] ++ if depth <= 0 then [] else
    [ (3, Compound "," <$> sequence [child, child]),
      (3, Compound ";" <$> sequence [child, child]),
      (2, Compound "once" . (: []) <$> child),
      (2, Compound "not" . (: []) <$> child),
      (2, Compound "call" . (: []) <$> child),
      (2, do condition <- child; yes <- child; no <- child
             pure (Compound ";" [Compound "->" [condition, yes], no])),
      (2, do goal <- child
             pure (Compound "findall" [Compound "pair" [Var 0, Var 1], goal, Var 3]))
    ]
  where
    child = genOpen (depth - 1)
    leaf = Gen.choice
      [ pure (Atom "true"), pure (Atom "fail"), pure (Atom "!"),
        pure (Compound "$cut" [IntLit (-7)]), pure (Compound "$cut" [Var 2]),
        pure (Compound "pick" [Var 0]), pure (Compound "pick" [Var 1]),
        pure (unify (Var 0) (Var 1)),
        unify (Var 0) <$> Gen.element [Atom "a", IntLit 1, Compound "box" [Var 1]],
        pure (unify (Var 2) (Compound "->" [Atom "true", Atom "fail"])),
        pure (unify (Var 2) (Compound "box" [Atom "!"])),
        pure (Atom "missing"), pure (Var 2),
        pure (Compound "is" [Var 0, Compound "div" [IntLit 1, IntLit 0]]),
        pure (Compound "write" [Atom "written"]),
        pure (Compound "call" [Atom "pick", Var 0]),
        pure (Compound "in" [mkList [Var 0, Var 1] Nothing, Compound "range" [IntLit 0, IntLit 2]]),
        pure (Compound "fd_lt" [Var 0, Var 1]),
        pure (Compound "label" [mkList [Var 0, Var 1] Nothing]),
        pure (Compound "tabled" [Var 0]),
        pure (Compound "assert" [Compound "memo" [Atom "kept"]]),
        pure (Compound "memo" [Var 1])
      ]

prop_open_controls_cuts_errors_and_fuel_match_both_engines :: Property
prop_open_controls_cuts_errors_and_fuel_match_both_engines = withTests 300 . property $ do
  goal <- forAll (genOpen 2)
  fuel <- forAll (Gen.int (Range.linear 0 5))
  let arguments = map Var [0 .. 3]
      clause = Clause (Compound "root" arguments) [conjoin (Atom "true") goal] 4
      query = Query [Compound ";" [Compound "root" arguments, unify (Var 0) (Atom "fallback")]]
        [("X", 0), ("Y", 1), ("Goal", 2), ("List", 3)] 4
  _ <- evalMaybe (compileClause clause)
  base <- load $ unlines
    [ "<- notable.", "root : nondet unsafe (any: <=>) (any: <=>) (any: <=>) (any: <=>).",
      "pick : nondet (any: <=>).", "pick 1.", "pick 1.", "pick 2.",
      "tabled : table nondet (int: <=>).", "tabled 1.", "tabled 2.",
      "memo : dynamic."
    ]
  let program = addClause clause base
      reference = Reference.solveQuery program query
      interpreted = Machine.solveQueryWithBackend Machine.Interpreted program query
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, metrics) <- evalEither (drain initial)
  events query actual === events query reference
  events query actual === events query interpreted
  rawStores actual === rawStores reference
  rawStores actual === rawStores interpreted
  assertCompiledControl metrics
  classify "compiled cut executed" (Machine.metricCompiledCuts metrics > 0)
  classify "error observed" (any isError actual)
  classify "foreign marker observed" (any isCut actual)
  assertFuelParity program query [fuel]
  assertTraceParity program query
  where
    isError (Reference.BranchError _) = True
    isError _ = False
    isCut (Reference.CutMarker _) = True
    isCut _ = False

values :: String -> Query -> Reference.Search -> [Term]
values name query items = [value | Reference.Found state <- items,
  Just value <- [lookup name (Reference.answerBindings (Reference.projectAnswer query state))]]

errors :: Reference.Search -> [SolveError]
errors items = [problem | Reference.BranchError problem <- items]

prop_raw_syntax_data_cuts_and_callable_expansion :: Property
prop_raw_syntax_data_cuts_and_callable_expansion = unit $ do
  base <- load "<- notable.\nroot : nondet unsafe (any: <=>)."
  let root body count = Clause (Compound "root" [Var 0]) body count
      fixtures =
        [ (root [conjoin (unify (Var 0) (Compound "box" [Atom "!"])) (Atom "true")] 1,
            [], [Compound "box" [Compound "$cut" [IntLit 1]]]),
          (root [unify (Var 1) (IntLit (-1)),
            Compound ";" [Compound "$cut" [Var 1], unify (Var 0) (Atom "kept")]] 2,
            [UnknownPredicate ("$cut", 1)], [Atom "kept"]),
          (root [unify (Var 1) (Compound "->" [Atom "true", Atom "fail"]),
            Compound ";" [Var 1, unify (Var 0) (Atom "kept")]] 2,
            [], [Atom "kept"]),
          (root [Compound "call" [Atom "true"]] 1, [UnknownPredicate ("true", 0)], []),
          (root [Compound "call" [IntLit 42]] 1, [TypeError "callable" (IntLit 42)], []),
          (root [Compound "call" [Var 1]] 2, [TypeError "callable" (Var 2)], []),
          (root [conjoin (Atom "true") (Var 1)] 2, [InstantiationError (Var 2)], [])
        ]
  forM_ fixtures $ \(clause, expectedErrors, expectedValues) -> do
    annotateShow clause
    _ <- evalMaybe (compileClause clause)
    let program = addClause clause base
    query <- queryText "root Result?"
    initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
    (actual, metrics) <- evalEither (drain initial)
    events query actual === events query (Reference.solveQuery program query)
    events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
    errors actual === expectedErrors
    values "Result" query actual === expectedValues
    Machine.metricCompiledCuts metrics === 0
    assertCompiledControl metrics
    assertTraceParity program query

prop_opaque_issue_and_output_policies_have_independent_expectations :: Property
prop_opaque_issue_and_output_policies_have_independent_expectations = unit $ do
  program <- load $ unlines
    [ "<- notable.",
      "first : nondet unsafe (any: <=>).", "first X <- once (missing ; X = kept ; late_missing).",
      "negative_success : nondet unsafe (any: <=>).",
      "negative_success X <- (not (missing ; true) ; X = fallback).",
      "negative_failure : nondet unsafe (any: <=>).",
      "negative_failure X <- (not (missing ; fail), X = never ; X = fallback).",
      "conditional : nondet unsafe (any: <=>).",
      "conditional X <- ((missing ; true) -> X = then ; missing_else).",
      "blocked : nondet unsafe (any: <=>).", "blocked X <- (missing -> X = then ; X = otherwise).",
      "collected : nondet unsafe (any: <=>).",
      "collected L <- findall X (missing ; X = kept ; late_missing) L.",
      "outputs : nondet unsafe (any: <=>).",
      "outputs L <- findall X ((write a, X = a) ; (write b, X = b)) L.",
      "shared : nondet unsafe (any: <=>) (any: <=>).",
      "shared X L <- findall (pair X Y) (Y = X ; true) L, X = retained."
    ]
  let missing = UnknownPredicate ("missing", 0)
      fixtures =
        [ ("first X?", "X", [missing], [Atom "kept"], [[]]),
          ("negative_success X?", "X", [], [Atom "fallback"], [[]]),
          ("negative_failure X?", "X", [missing], [Atom "fallback"], [[]]),
          ("conditional X?", "X", [missing], [Atom "then"], [[]]),
          ("blocked X?", "X", [missing], [], []),
          ("collected L?", "L", [missing], [], []),
          ("outputs L?", "L", [], [mkList [Atom "a", Atom "b"] Nothing],
            [[Reference.WriteEvent "a", Reference.WriteEvent "b"]])
        ]
  forM_ fixtures $ \(source, name, expectedErrors, expectedValues, expectedOutputs) -> do
    query <- queryText source
    actual <- compareQuery program query
    errors actual === expectedErrors
    values name query actual === expectedValues
    [Reference.answerOutput (Reference.projectAnswer query state) | Reference.Found state <- actual] === expectedOutputs
    assertTraceParity program query
    assertFuelParity program query [0, 1, 2, 3, 5]
  sharedQuery <- queryText "shared X L?"
  shared <- compareQuery program sharedQuery
  case [Reference.projectAnswer sharedQuery state | Reference.Found state <- shared] of
    [answer] -> do
      lookup "X" (Reference.answerBindings answer) === Just (Atom "retained")
      case lookup "L" (Reference.answerBindings answer) of
        Just list -> case unfoldCons list of
          ([Compound "pair" [Atom "retained", Atom "retained"],
            Compound "pair" [Atom "retained", Var _]], Nothing) -> pure ()
          other -> annotateShow other >> failure
        Nothing -> failure
    other -> annotateShow other >> failure

prop_owned_foreign_and_committing_cut_barriers :: Property
prop_owned_foreign_and_committing_cut_barriers = unit $ do
  let foreignCut = Compound "$cut" [IntLit (-7)]
      result value = unify (Var 0) (Atom value)
      clause body = Clause (Compound "p" [Var 0]) body 1
      sibling = Clause (Compound "p" [Atom "second"]) [] 0
      scenarios =
        [ ([foreignCut, result "first"], [Atom "first"], [-7], 1),
          ([foreignCut, Atom "!", result "first"], [Atom "first", Atom "outer"], [], 2),
          ([foreignCut, Atom "!", Atom "fail"], [Atom "outer"], [], 2)
        ]
  base <- load "<- notable.\np : nondet unsafe (any: <=>)."
  query <- queryText "(p X ; X = outer)?"
  forM_ scenarios $ \(body, expectedValues, expectedMarkers, expectedCuts) -> do
    let program = addClause sibling (addClause (clause body) base)
    initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
    (actual, metrics) <- evalEither (drain initial)
    events query actual === events query (Reference.solveQuery program query)
    events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
    values "X" query actual === expectedValues
    errors actual === []
    [owner | Reference.CutMarker owner <- actual] === expectedMarkers
    Machine.metricCompiledCuts metrics === expectedCuts
    assertCompiledControl metrics
    assertTraceParity program query
  -- A checked first-success contract may discard a foreign marker, including
  -- one parked behind a noncommitting helper return. If no checked answer is
  -- found, its required-success guard must survive the cut.
  forM_ [(Semidet, "semidet"), (Det, "det")] $ \(determinism, declaration) ->
    forM_ [False, True] $ \throughHelper -> forM_ [False, True] $ \fails -> do
      declared <- load ("<- notable.\np : " ++ declaration ++ " unsafe (atom: =>).\nmarker : nondet unsafe.")
      let markerClause = Clause (Atom "marker") [foreignCut] 0
          invocation = if throughHelper then Atom "marker" else foreignCut
          body = [invocation, if fails then Atom "fail" else result "first"]
          program = addClause markerClause (addClause sibling (addClause (clause body) declared))
      initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
      (actual, metrics) <- evalEither (drain initial)
      events query actual === events query (Reference.solveQuery program query)
      events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
      values "X" query actual === if fails then [Atom "outer"] else [Atom "first", Atom "outer"]
      errors actual === [DetError ("p", 1) Det 0 | fails && determinism == Det]
      [owner | Reference.CutMarker owner <- actual] === []
      assert (Machine.metricCompiledCuts metrics > 0)
      assertCompiledControl metrics
      assertTraceParity program query
  plain <- evalEither (Machine.startWithBackend Machine.Bytecode
    (addClause (clause [Atom "!", result "first"]) base) query)
  (_, disabled) <- evalEither (drain plain)
  Machine.metricCompiledControlInstructions disabled === 0
  Machine.metricCompiledCuts disabled === 0

prop_output_validation_precedes_commit_and_required_success :: Property
prop_output_validation_precedes_commit_and_required_success = unit $ do
  forM_ [("semidet", False), ("det", False), ("semidet", True), ("det", True)] $ \(declaration, localCut) -> do
    program <- load $ unlines
      [ "<- notable.", "p : " ++ declaration ++ " unsafe (int: =>).",
        "p X <- (" ++ (if localCut then "true, !" else "true") ++ " ; X = 7 ; X = 8).",
        "p 9."
      ]
    query <- queryText "(p X ; X = outer)?"
    initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
    (actual, metrics) <- evalEither (drain initial)
    events query actual === events query (Reference.solveQuery program query)
    events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
    errors actual === [OutputModeError ("p", 1) 1 (Var 0)] ++
      [DetError ("p", 1) Det 0 | localCut && declaration == "det"]
    values "X" query actual === if localCut then [Atom "outer"] else [IntLit 7, Atom "outer"]
    when localCut (assert (Machine.metricCompiledCuts metrics > 0))
    assertCompiledControl metrics
    assertTraceParity program query
    assertFuelParity program query [0, 1, 2, 3, 5]

untakenArm :: Term
untakenArm = foldr conjoin (Atom "true")
  [Compound "sink" [Compound ("future_constructor_" ++ show index)
    [StrLit ("future_scalar_" ++ show index), IntLit (fromIntegral index), Var 0]]
    | index <- [0 :: Int .. 1999]]

prop_untaken_control_arms_never_materialize_their_data :: Property
prop_untaken_control_arms_never_materialize_their_data = unit $ do
  base <- load "<- notable.\nroot : nondet unsafe (any: <=>).\nsink _."
  let kept = unify (Var 0) (Atom "kept")
      bodies =
        [ Compound ";" [Compound "->" [Atom "true", kept], untakenArm],
          Compound ";" [Compound "->" [Atom "fail", untakenArm], kept],
          Compound "once" [Compound ";" [kept, untakenArm]],
          Compound ";" [conjoin kept (Atom "!"), untakenArm],
          conjoin (Compound "not" [Compound ";" [Atom "true", untakenArm]]) kept
        ]
      query = Query [Compound ";" [Compound "root" [Var 0], unify (Var 0) (Atom "outer")]] [("Result", 0)] 1
  forM_ (zip [0 :: Int ..] bodies) $ \(index, body) -> do
    let clause = Clause (Compound "root" [Var 0]) [body] 1
        program = addClause clause base
    _ <- evalMaybe (compileClause clause)
    initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
    (actual, metrics) <- evalEither (drain initial)
    events query actual === events query (Reference.solveQuery program query)
    events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
    values "Result" query actual === if index == 4 then [Atom "outer"] else [Atom "kept", Atom "outer"]
    errors actual === []
    assertCompiledControl metrics
    assert (Machine.metricBodyAllocationInstructions metrics <= 12)
    assert (Machine.metricMaxActivationRegisters metrics <= 4)
    assert (Machine.metricMaxHeapCells metrics <= 128)
    assert (Machine.metricMaxTasks metrics <= 24)
    assert (Machine.metricMaxConstants metrics <= 12)
    assert (Machine.metricMaxFunctors metrics <= 12)

prop_pending_control_locals_survive_collection_and_last_goal_tail_calls :: Property
prop_pending_control_locals_survive_collection_and_last_goal_tail_calls = unit $ do
  program <- load $ unlines
    [ "<- notable.", "hold (pair retained retained).", "make (box fresh).",
      "combine Left Right (pair Left Right).", "root : nondet unsafe (any: <=>).",
      "root Result <- hold Shared, (true -> (down 10000 _, make Future, combine Shared Future Result) ; missing).",
      "down 0 done.", "down N Result <- N > 0, M is N - 1, down M Result."
    ]
  query <- queryText "root Result?"
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, metrics) <- evalEither (drain initial)
  events query actual === events query (Reference.solveQuery program query)
  events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
  values "Result" query actual === [Compound "pair"
    [Compound "pair" [Atom "retained", Atom "retained"], Compound "box" [Atom "fresh"]]]
  errors actual === []
  assertCompiledControl metrics
  assert (Machine.metricCollections metrics > 0)
  assert (Machine.metricTailCalls metrics >= 9000)
  assert (Machine.metricMaxTasks metrics <= 24)
  assert (Machine.metricMaxHeapCells metrics <= 4096)

prop_interleaved_control_checkpoints_and_generic_meta_metadata :: Property
prop_interleaved_control_checkpoints_and_generic_meta_metadata = unit $ do
  program <- load $ unlines
    [ "<- notable.", "pick a.", "pick b.", "wrap X (pair X X).",
      "root : nondet unsafe (any: <=>).",
      "root Result <- ((missing ; pick X), once (wrap X Mid), (true -> wrap Mid Result ; fail)).",
      "meta : nondet unsafe (any: <=>).",
      "meta List <- forall (pick X) (nonvar X), findall X (pick X) List.",
      "best : nondet (int: =>).", "best Cost <- minimize Cost (Cost = 3 ; Cost = 1 ; Cost = 2).",
      "memo : dynamic.", "dynamic : nondet unsafe (any: <=>).",
      "dynamic Result <- (assert (memo retained), once (memo Result) ; Result = fallback).",
      "tabled : table nondet (int: <=>).", "tabled 1.", "tabled 2.",
      "constrained : nondet (any: <=>).",
      "constrained List <- X in 1..3, findall X (tabled X, label [X]) List, label [X]."
    ]
  forM_ ["root Result?", "meta List?", "best Cost?", "dynamic Result?", "constrained List?"] $ \source -> do
    query <- queryText source
    _ <- compareQuery program query
    assertTraceParity program query
    assertFuelParity program query [0, 1, 2, 3, 5]
  query <- queryText "root Result?"
  compiled <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  interpreted <- evalEither (Machine.startWithBackend Machine.Interpreted program query)
  first <- evalEither (Machine.resume compiled)
  oldFirst <- evalEither (Machine.resume interpreted)
  case (first, oldFirst) of
    (Machine.Yield retained next, Machine.Yield oldRetained oldNext) -> do
      let before = events query [retained]
      _ <- evalIO (evaluate (length (show before)))
      (oldRest, _) <- evalEither (drain oldNext)
      (rest, _) <- evalEither (drain next)
      (repeated, _) <- evalEither (drain next)
      (allAgain, _) <- evalEither (drain compiled)
      events query rest === events query oldRest
      events query rest === events query repeated
      before === events query [retained]
      before === events query [oldRetained]
      before ++ events query rest === events query allAgain
      events query allAgain === events query (Reference.solveQuery program query)
    _ -> failure

machineCompiledControlGroup :: Group
machineCompiledControlGroup = Group "compiled nested control and cut barriers"
  [ ("closed control trees match an independent ordered model", prop_closed_control_trees_match_independent_model)
  , ("open controls cuts errors fuel and traces match both engines", prop_open_controls_cuts_errors_and_fuel_match_both_engines)
  , ("raw syntax data cuts and callable expansion remain compatible", prop_raw_syntax_data_cuts_and_callable_expansion)
  , ("opaque issue output and findall sharing policies remain compatible", prop_opaque_issue_and_output_policies_have_independent_expectations)
  , ("owned foreign and committing cut barriers preserve their boundaries", prop_owned_foreign_and_committing_cut_barriers)
  , ("output validation precedes commit and required-success checks", prop_output_validation_precedes_commit_and_required_success)
  , ("untaken control arms never materialize their data", prop_untaken_control_arms_never_materialize_their_data)
  , ("pending control locals survive collection and last-goal tail calls", prop_pending_control_locals_survive_collection_and_last_goal_tail_calls)
  , ("interleaved control checkpoints and generic meta metadata", prop_interleaved_control_checkpoints_and_generic_meta_metadata)
  ]
