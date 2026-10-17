{-# LANGUAGE OverloadedStrings #-}

-- Successful opaque searches may hand their exact heap/bindings to a parked
-- caller only while the heap lineage is unchanged. Keep complete short-search
-- stores as the oracle, and separately exercise restoration and collection.
module MachineOpaqueScopeTest (machineOpaqueScopeGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Float (castDoubleToWord64)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import qualified Infera.Machine.Tail as Tail
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program
import Infera.Syntax
import qualified Infera.Unify as Unify
import System.Timeout (timeout)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText source = annotate source >> evalEither (parseQuery source)

bits :: Term -> Term
bits (FloatLit value) = Compound "$opaque_float_bits"
  [IntLit (fromIntegral (castDoubleToWord64 value))]
bits (Compound name arguments) = Compound name (map bits arguments)
bits value = value

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

mapError :: (Term -> Term) -> SolveError -> SolveError
mapError transform problem = case problem of
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

type Tables = Map.Map Term
  (Bool, Bool, [(Term, Int, [Reference.OutputEvent])], Set.Set Term)

tables :: Reference.SolverState -> Tables
tables = Map.mapKeys bits . Map.map entry . Reference.ssTables
  where
    entry table = (Reference.teComplete table, Reference.teTruncated table,
      [(bits term, count, output) | (term, count, output) <- Reference.teAnswers table],
      Set.map bits (Reference.teSet table))

canonical :: Query -> [Term] -> [Term]
canonical query terms = case fst (Unify.canonicalize Unify.emptySubst root) of
  Compound _ values -> map bits (drop (length names) values)
  _ -> error "canonicalization changed an opaque-search root"
  where
    names = map (Var . snd) (queryNames query)
    root = Compound "$opaque_roots" (names ++ terms)

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent] Store Int Int Tables
      (Map.Map PredKey [(Term, Int)])
  | Error SolveError | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

events :: Query -> Reference.Search -> [Event]
events query = map event
  where
    normalize term = case canonical query [term] of
      [value] -> value
      _ -> error "canonicalization changed an opaque-search arity"
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
         in Answer (zip (map fst bindings) (canonical query (map snd bindings)))
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
              (storeBits ((Reference.ssStore state) {stSubst = Unify.emptySubst}))
              (Reference.ssFresh state) (Reference.ssOutLen state) (tables state)
              (Map.map (map (\(term, count) -> (bits term, count))) (Reference.ssDynamic state))
      Reference.BranchError problem -> Error (mapError normalize problem)
      Reference.BranchExhausted -> Exhausted
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete (bits (fst (Unify.canonicalize Unify.emptySubst key)))

rawStores :: Reference.Search -> [Store]
rawStores items = [storeBits (Reference.ssStore state) | Reference.Found state <- items]

drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Metrics)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], Machine.checkpointMetrics checkpoint)
    Machine.Yield item next -> do
      (rest, metrics) <- drain next
      pure (item : rest, metrics)

compareQuery :: Bool -> Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
compareQuery exact program query = do
  let expected = Reference.solveQuery program query
  forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
    let actual = Machine.solveQueryWithBackend backend program query
    events query actual === events query expected
    if exact then rawStores actual === rawStores expected else pure ()
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  result'@(actual, _) <- evalEither (drain initial)
  events query actual === events query expected
  if exact then rawStores actual === rawStores expected else pure ()
  pure result'

traceSearch :: Machine.Checkpoint -> Either Heap.HeapError ([Trace.TraceEvent], Reference.Search)
traceSearch checkpoint = do
  (trace, step) <- Machine.resumeTraced checkpoint
  case step of
    Machine.Finished -> pure (trace, [])
    Machine.Yield item next -> do
      (laterTrace, later) <- traceSearch next
      pure (trace ++ laterTrace, item : later)

assertTrace :: Program -> Query -> PropertyT IO ()
assertTrace program query = do
  compiled <- evalEither (Machine.startTracedWithBackend Machine.Bytecode program query)
  interpreted <- evalEither (Machine.startTracedWithBackend Machine.Interpreted program query)
  (trace, actual) <- evalEither (traceSearch compiled)
  (oldTrace, expected) <- evalEither (traceSearch interpreted)
  let normalize = map (\event -> event {Trace.traceGoal = bits (Trace.traceGoal event),
        Trace.traceError = mapError bits <$> Trace.traceError event})
  normalize trace === normalize oldTrace
  events query actual === events query expected
  (againTrace, again) <- evalEither (traceSearch compiled)
  normalize againTrace === normalize trace
  events query again === events query actual

andAlso :: [Term] -> Term
andAlso = foldr (\left right -> Compound "," [left, right]) (Atom "true")

equal :: Term -> Term -> Term
equal left right = Compound "unify" [left, right]

conditional :: Term -> Term -> Term -> Term
conditional condition yes no = Compound ";" [Compound "->" [condition, yes], no]

prop_generated_successful_scope_aliases_and_raw_stores :: Property
prop_generated_successful_scope_aliases_and_raw_stores = withTests 200 . property $ do
  depth <- forAll (Gen.int (Range.linear 1 7))
  maximum' <- forAll (Gen.int (Range.linear 0 4))
  labelDomain <- forAll Gen.bool
  anchor <- forAll (Gen.element [Nothing, Just (Atom "leaf"), Just (IntLit 5), Just (FloatLit (-0.0))])
  let local index = Var (4 + index * 2)
      alias index = Var (5 + index * 2)
      stage index = Compound "once" [andAlso
        [ equal (local index) (Compound "pair" [Var 1, Var 2]),
          conditional (Compound "once" [equal (alias index) (local index)])
            (equal (alias index) (Compound "pair" [Var 2, Var 1])) (Atom "fail")
        ]]
      body =
        [Compound "in" [Var 3, Compound "range" [IntLit 0, IntLit (fromIntegral maximum')]],
         equal (Var 2) (Var 1)] ++ map stage [0 .. depth - 1] ++
        [equal (Var 0) (Compound "packet" [mkList (map local [0 .. depth - 1]) Nothing, Var 3])] ++
        maybe [] (\value -> [equal (Var 1) value]) anchor ++
        [Compound "label" [mkList [Var 3] Nothing] | labelDomain]
      clause = Clause (Compound "root" (map Var [0 .. 3])) body (4 + 2 * depth)
      program = buildProgram [TLDirective [Atom "notable"], TLClause clause]
      query = Query [Compound ";" [Compound "root" (map Var [0 .. 3]), equal (Var 0) (Atom "outer")]]
        [("Result", 0), ("X", 1), ("Alias", 2), ("Domain", 3)] 4
  (_, metrics) <- compareQuery True program query
  assert (Machine.metricScopeHandoffs metrics >= 3 * depth)
  Machine.metricScopeReplays metrics === 0
  classify "domain remains residual" (not labelDomain)
  classify "alias remains open" (anchor == Nothing)

prop_buffered_issues_output_dynamic_tables_and_cuts :: Property
prop_buffered_issues_output_dynamic_tables_and_cuts = unit $ do
  program <- load $ unlines
    [ "<- notable.", "memo : dynamic.",
      "cached : table nondet (int: <=>).", "cached 1.", "cached 2.",
      "effect : nondet unsafe (any: <=>).",
      "effect X <- once (write retained, assert (memo first), X = first), memo X.",
      "choose : nondet unsafe (any: <=>).",
      "choose X <- (once (true, !, X = first) ; X = second)."
    ]
  forM_
    [ "once (missing ; X = kept ; late_missing), (X = kept ; X = other)?",
      "((missing ; X = kept) -> Y = X ; Y = otherwise)?",
      "(missing -> X = never ; X = otherwise)?",
      "(not (missing ; true), X = never ; X = outer)?",
      "(not (missing ; fail), X = never ; X = outer)?",
      "once (X is 1 / 0 ; X = kept), X = kept?",
      "effect X?", "choose X?",
      "once (cached X), cached Y?",
      "assert (memo old), (once (retract (memo X)) -> assert (memo new) ; fail), memo Y?",
      "(once (write discarded, assert (memo bad), fail) ; write retained), not (memo X)?",
      "once (A = (box X), B = A), X in 1..2, Y #= X + 1, label [X, Y]?",
      "once (not (X = discarded, fail)), X = retained?"
    ] $ \source -> do
      query <- queryText source
      _ <- compareQuery True program query
      assertTrace program query

prop_restored_and_collected_children_replay_selected_state :: Property
prop_restored_and_collected_children_replay_selected_state = unit $ do
  program <- load $ unlines
    [ "<- notable.", "down 0 done.",
      "down N Result <- N > 0, M is N - 1, down M Result."
    ]
  forM_
    [ "once (fail ; A = (box X), B = A), X = retained, A = B?",
      "((fail ; A = (box X), B = A) -> X = retained ; fail), A = B?",
      "once (A = (box X), B = A, down 4000 R), X = retained, A = B?",
      "((A = (box X), B = A, down 4000 R) -> X = retained ; fail), A = B?",
      "once (call ((X = bad, fail) ; X = kept)), X = kept?"
    ] $ \source -> do
      query <- queryText source
      (_, metrics) <- compareQuery False program query
      annotateShow metrics
      assert (Machine.metricScopeReplays metrics > 0)
  -- A collected child must preserve the parent's live retry heap as well as
  -- child aliases; on retry, neither accepted child bindings nor its locals leak.
  query <- queryText "(A = (box X), once (B = A, down 4000 R), X = retained ; A = fallback), A = A?"
  (actual, metrics) <- compareQuery False program query
  assert (Machine.metricCollections metrics > 0)
  assert (Machine.metricScopeReplays metrics > 0)
  length [() | Reference.Found _ <- actual] === 2

prop_retained_interleaved_and_traced_scope_checkpoints :: Property
prop_retained_interleaved_and_traced_scope_checkpoints = unit $ do
  program <- load $ unlines
    [ "<- notable.", "pick first.", "pick second.", "wrap X (pair X X).",
      "root Result <- call (pick X), once (wrap X Mid), (true -> wrap Mid Result ; fail)."
    ]
  query <- queryText "(root Result ; Result = fallback)?"
  compiled <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  independent <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  first <- evalEither (Machine.resume compiled)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = events query [retained]
      _ <- evalIO (evaluate (length (show before)))
      (interleaved, _) <- evalEither (drain independent)
      (rest, metrics) <- evalEither (drain next)
      (repeated, repeatedMetrics) <- evalEither (drain next)
      (restarted, _) <- evalEither (drain compiled)
      before === events query [retained]
      events query rest === events query repeated
      metrics === repeatedMetrics
      before ++ events query rest === events query restarted
      events query restarted === events query interleaved
      events query restarted === events query (Reference.solveQuery program query)
      rawStores restarted === rawStores (Reference.solveQuery program query)
      assert (Machine.metricScopeHandoffs metrics > 0)
  assertTrace program query

prop_resolution_fuel_is_preserved_through_completed_controls :: Property
prop_resolution_fuel_is_preserved_through_completed_controls = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 0 12))
  budget <- forAll (Gen.int (Range.linear 0 15))
  program <- load $ unlines
    [ "<- notable.", "loop 0 done.",
      "loop N R <- N > 0, once (M is N - 1), (not (M < 0) -> loop M R ; R = bad).",
      "blocked X <- once (loop 100 X)."
    ]
  query <- queryText ("once (loop " ++ show count ++ " R), (R = done ; R = other)?")
  let environment = Reference.mkEnv program
      state = Reference.initialState (queryNVars query)
      expected = Reference.solveGoals environment budget state (queryGoals query)
  forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
    initial <- evalEither (Machine.startGoalsWithBackend backend environment budget state (queryGoals query))
    (actual, _) <- evalEither (drain initial)
    events query actual === events query expected
    rawStores actual === rawStores expected
  -- An exhausted condition cannot be turned into a successful else branch.
  blocked <- queryText "(blocked R -> R = then ; R = otherwise)?"
  let blockedState = Reference.initialState (queryNVars blocked)
      expectedBlocked = Reference.solveGoals environment budget blockedState (queryGoals blocked)
  initial <- evalEither (Machine.startGoalsWithBackend Machine.Bytecode environment budget blockedState (queryGoals blocked))
  (actualBlocked, _) <- evalEither (drain initial)
  events blocked actualBlocked === events blocked expectedBlocked
  assert (any exhausted actualBlocked)
  assert (null [() | Reference.Found _ <- actualBlocked])
  where
    exhausted Reference.BranchExhausted = True
    exhausted _ = False

prop_long_collected_default_scopes_and_incomplete_dependencies :: Property
prop_long_collected_default_scopes_and_incomplete_dependencies = unit $ do
  program <- load $ unlines
    [ "<- notable.", "loop 0 done.",
      "loop N R <- N > 0, once (M is N - 1), (not (M < 0) -> loop M R ; R = bad).",
      "cached : table.", "cached 1."
    ]
  forM_ [999, 1000, 1001 :: Int] $ \count ->
    forM_
      [ "once (loop " ++ show count ++ " R)?",
        "(loop " ++ show count ++ " R -> R = done ; R = otherwise)?",
        "not (loop " ++ show count ++ " R, fail)?"
      ] $ \source -> do
        query <- queryText source
        _ <- compareQuery False program query
        pure ()
  forM_
    [ "once (cached X), X = 1?",
      "(cached X -> X = 1 ; X = missing)?",
      "not (cached X)?",
      "not (cached X, fail), X = retained?"
    ] $ \source -> do
      query <- queryText source
      let key = Compound "cached" [Var 0]
          answer = Compound "cached" [IntLit 1]
          entry = Reference.TableEntry False False [(answer, 0, [])] (Set.singleton answer)
          state = (Reference.initialState (queryNVars query)) {Reference.ssTables = Map.singleton key entry}
          environment = Reference.mkEnv program
          expected = Reference.solveGoals environment 8 state (queryGoals query)
      assert (any dependency expected)
      forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
        initial <- evalEither (Machine.startGoalsWithBackend backend environment 8 state (queryGoals query))
        (actual, _) <- evalEither (drain initial)
        events query actual === events query expected
        rawStores actual === rawStores expected
  where
    dependency (Reference.ConsumedIncomplete _) = True
    dependency _ = False

-- startGoals intentionally disables physical frame retirement. Exercise the
-- real default entry point too: a newly eligible scoped loop must retire
-- frames without inheriting the historic first-order fuel refund. Zero locals
-- avoid building a 100000-entry substitution in the independent oracle.
prop_default_budget_is_not_refunded_by_new_control_proof :: Property
prop_default_budget_is_not_refunded_by_new_control_proof = unit $ do
  program <- load "<- notable.\nbudget_loop <- once (true), budget_loop."
  query <- queryText "budget_loop?"
  let expected = Reference.solveQuery program query
      forceWithinBudget value = do
        finished <- evalIO (timeout (30 * 1000000) (evaluate (length (show value))))
        _ <- evalMaybe finished
        pure ()
  forceWithinBudget (events query expected)
  events query expected === [Exhausted]
  forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
    annotateShow backend
    let normal = events query (Machine.solveQueryWithBackend backend program query)
    forceWithinBudget normal
    normal === events query expected
    initial <- evalEither (Machine.startMeasuredWithBackend backend program query)
    let result' = drain initial
    forceWithinBudget (fmap (\(items, metrics) -> (events query items, metrics)) result')
    (actual, metrics) <- evalEither result'
    events query actual === events query expected
    annotateShow metrics
    Machine.metricCalls metrics === Reference.maxResolutionDepth + 1
    assert (Machine.metricTailCalls metrics >= Reference.maxResolutionDepth - 1)
    assert (Machine.metricMaxTasks metrics <= 8)
    assert (Machine.metricMaxScopes metrics <= 1)
    assert (Machine.metricScopeHandoffs metrics >= Reference.maxResolutionDepth)

prop_completed_pure_controls_allow_tail_reuse_but_hazards_do_not :: Property
prop_completed_pure_controls_allow_tail_reuse_but_hazards_do_not = unit $ do
  program <- load $ unlines
    [ "<- notable.", "loop 0 done.",
      "loop N R <- N > 0, once (M is N - 1), (not (M < 0) -> loop M R ; R = bad).",
      "memo : dynamic.", "cached : table.", "cached value.",
      "unsafe_helper : unsafe.", "unsafe_helper <- write effect."
    ]
  definition <- evalMaybe (lookupPred ("loop", 2) program)
  Tail.eligiblePredicate program definition === True
  query <- queryText "loop 600 R?"
  (_, metrics) <- compareQuery False program query
  annotateShow metrics
  assert (Machine.metricTailCalls metrics >= 500)
  assert (Machine.metricMaxTasks metrics <= 32)
  assert (Machine.metricMaxScopes metrics <= 2)
  assert (Machine.metricCollections metrics > 0)
  forM_
    [ Compound "once" [Compound "call" [Atom "true"]],
      Compound "not" [Compound "write" [Atom "effect"]],
      conditional (Atom "true") (Atom "true") (Atom "unsafe_helper"),
      Compound ";" [Atom "true", Compound "memo" [Var 0]],
      conditional (Atom "fail") (Compound "cached" [Var 0]) (Atom "true"),
      Compound "once" [andAlso [Atom "true", Atom "!"]],
      Compound "not" [Compound "$cut" [IntLit 3]],
      Compound "once" [Var 0],
      Compound "once" [Atom "unknown"]
    ] $ \hazard -> do
      let clause = Clause (Compound "hazard" [Var 0]) [hazard] 1
          poisoned = addClause clause program
      target <- evalMaybe (lookupPred ("hazard", 1) poisoned)
      annotateShow hazard
      Tail.eligiblePredicate poisoned target === False

machineOpaqueScopeGroup :: Group
machineOpaqueScopeGroup = Group "opaque scope handoff and completed pure control"
  [ ("generated successful scope aliases preserve complete stores", prop_generated_successful_scope_aliases_and_raw_stores),
    ("buffered issues output dynamic tables and cuts retain their policy", prop_buffered_issues_output_dynamic_tables_and_cuts),
    ("restored and collected children replay their selected state", prop_restored_and_collected_children_replay_selected_state),
    ("retained interleaved and traced scope checkpoints replay independently", prop_retained_interleaved_and_traced_scope_checkpoints),
    ("completed control scopes preserve resolution fuel", prop_resolution_fuel_is_preserved_through_completed_controls),
    ("long collected default scopes and incomplete dependencies are preserved", prop_long_collected_default_scopes_and_incomplete_dependencies),
    ("new completed control proof preserves the real default budget", prop_default_budget_is_not_refunded_by_new_control_proof),
    ("completed pure control enables tail reuse and rejects nested hazards", prop_completed_pure_controls_allow_tail_reuse_but_hazards_do_not)
  ]
