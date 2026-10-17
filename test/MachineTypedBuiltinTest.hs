{-# LANGUAGE OverloadedStrings #-}

-- Typed builtin operands are an allocation/dispatch optimization. The source
-- interpreter remains an independent oracle for ordered events and complete
-- branch state, while finite arithmetic/CLP models protect against shared bugs.
module MachineTypedBuiltinTest (machineTypedBuiltinGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP
import Infera.Compile hiding (Cut)
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.Bytecode as Bytecode
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program (Program, addClause, addDecl)
import Infera.Syntax
import qualified Infera.Unify as Unify

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

must :: Show problem => ST s (Either problem value) -> ST s value
must action = action >>= either (error . show) pure

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

bits :: Term -> Term
bits (FloatLit number) = Compound "$typed_builtin_float_bits"
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

errorBits :: SolveError -> SolveError
errorBits problem = case problem of
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

-- No variable canonicalization: raw substitution direction, local IDs, fresh
-- counts, output order and every CLP scheduler field must agree exactly.
events :: Query -> Reference.Search -> [Event]
events query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
         in Answer [(name, bits term) | (name, term) <- Reference.answerBindings answer]
              (Reference.answerResiduals answer) (Reference.ssOutput state)
              (storeBits (Reference.ssStore state)) (Reference.ssFresh state)
              (Reference.ssOutLen state) (tableMetadata state)
              (Map.map (map (\(term, count) -> (bits term, count))) (Reference.ssDynamic state))
      Reference.BranchError problem -> Error (errorBits problem)
      Reference.BranchExhausted -> Exhausted
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete (bits key)

drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Metrics)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], Machine.checkpointMetrics checkpoint)
    Machine.Yield item next -> do
      (remaining, metrics) <- drain next
      pure (item : remaining, metrics)

compareAll :: Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
compareAll program query = do
  normal <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  measured <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, disabled) <- evalEither (drain normal)
  (counted, metrics) <- evalEither (drain measured)
  events query actual === events query (Reference.solveQuery program query)
  events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
  events query counted === events query actual
  disabled === Machine.checkpointMetrics normal
  Machine.metricTypedBuiltinCalls disabled === 0
  Machine.metricBuiltinWrappersAvoided disabled === 0
  pure (actual, metrics)

assertTyped :: Machine.Metrics -> PropertyT IO ()
assertTyped metrics = do
  assert (Machine.metricCompiledActivations metrics > 0)
  assert (Machine.metricTypedBuiltinCalls metrics > 0)
  assert (Machine.metricBuiltinWrappersAvoided metrics > 0)

drainTraced :: Machine.Checkpoint -> Either Heap.HeapError ([Trace.TraceEvent], Reference.Search)
drainTraced checkpoint = do
  (trace, step) <- Machine.resumeTraced checkpoint
  case step of
    Machine.Finished -> pure (trace, [])
    Machine.Yield item next -> do
      (laterTrace, later) <- drainTraced next
      pure (trace ++ laterTrace, item : later)

assertTraceParity :: Program -> Query -> PropertyT IO ()
assertTraceParity program query = do
  native <- evalEither (Machine.startTracedWithBackend Machine.Bytecode program query)
  old <- evalEither (Machine.startTracedWithBackend Machine.Interpreted program query)
  (trace, actual) <- evalEither (drainTraced native)
  (oldTrace, expected) <- evalEither (drainTraced old)
  trace === oldTrace
  events query actual === events query expected
  (againTrace, again) <- evalEither (drainTraced native)
  againTrace === trace
  events query again === events query actual

app :: String -> [Term] -> Term
app = Compound

list :: [Term] -> Term
list terms = mkList terms Nothing

unify :: Term -> Term -> Term
unify left right = app "unify" [left, right]

rootQuery :: Query
rootQuery = Query [app "root" [Var 0]] [("Result", 0)] 1

rootBase :: PropertyT IO Program
rootBase = load "<- notable.\nroot : nondet unsafe (any: <=>)."

addRoot :: Program -> [Term] -> Int -> Program
addRoot program goals count = addClause (Clause (app "root" [Var 0]) goals count) program

values :: String -> Query -> Reference.Search -> [Term]
values name query items = [value | Reference.Found state <- items,
  Just value <- [lookup name (Reference.answerBindings (Reference.projectAnswer query state))]]

errors :: Reference.Search -> [SolveError]
errors items = [problem | Reference.BranchError problem <- items]

prop_generated_arithmetic_sparse_aliases_and_controls :: Property
prop_generated_arithmetic_sparse_aliases_and_controls = withTests 200 . property $ do
  left <- forAll (Gen.integral (Range.linear (-20) 20))
  right <- forAll (Gen.integral (Range.linear (-20) 20))
  operator <- forAll (Gen.element ["plus", "minus", "mul", "min", "max"])
  wrapper <- forAll (Gen.int (Range.linear 0 3))
  let expected = case operator of
        "plus" -> left + right
        "minus" -> left - right
        "mul" -> left * right
        "min" -> min left right
        _ -> max left right
      calculation = app "is" [Var 13, app operator [Var 499, IntLit right]]
      result = unify (Var 0) (app "pair" [Var 13, Var 37])
      combined = app "," [calculation, app "," [app "gte" [Var 13, IntLit expected], result]]
      body = case wrapper of
        1 -> app "once" [combined]
        2 -> app ";" [combined, combined]
        3 -> app ";" [app "->" [app "equiv" [Var 37, IntLit left], combined], Atom "missing"]
        _ -> combined
      multiplicity = if wrapper == 2 then 2 else 1
  base <- rootBase
  let program = addRoot base [unify (Var 37) (IntLit left), unify (Var 499) (Var 37), body] 500
  (actual, metrics) <- compareAll program rootQuery
  values "Result" rootQuery actual === replicate multiplicity (app "pair" [IntLit expected, IntLit left])
  errors actual === []
  [Reference.ssFresh state | Reference.Found state <- actual] === replicate multiplicity 501
  assertTyped metrics
  classify "sparse operands inside opaque control" (wrapper /= 0)

prop_generated_clp_posting_and_independent_finite_model :: Property
prop_generated_clp_posting_and_independent_finite_model = withTests 150 . property $ do
  lo <- forAll (Gen.integral (Range.linear (-2) 0))
  hi <- forAll (Gen.integral (Range.linear 0 2))
  hole <- forAll (Gen.integral (Range.linear (-2) 2))
  cap <- forAll (Gen.integral (Range.linear 0 4))
  distinct <- forAll Gen.bool
  let x = Var 37; y = Var 499; truth = Var 13; distance = Var 31
      goals =
        [ app "in" [list [x, y], app "range" [IntLit lo, IntLit hi]],
          app "fd_ne" [x, IntLit hole],
          app "reify" [app "fd_lt" [x, y], truth],
          app "int_eq" [distance, app "abs" [app "minus" [x, y]]],
          app "fd_le" [distance, IntLit cap]
        ] ++ [app "all_distinct" [list [x, y]] | distinct] ++
        [app "label" [list [x, y, truth, distance]], unify (Var 0) (app "row" [x, y, truth, distance])]
      expected = sort [app "row" (map IntLit [a, b, if a < b then 1 else 0, abs (a - b)])
        | a <- [lo .. hi], b <- [lo .. hi], a /= hole, not distinct || a /= b, abs (a - b) <= cap]
      completed = Atom "$typed_clp_completed"
      query = Query [app ";" [app "root" [Var 0], unify (Var 0) completed]] [("Result", 0)] 1
  base <- rootBase
  -- A trailing answer exposes the accumulated metrics even when every CLP
  -- branch fails: Finished itself carries no final checkpoint. The entire
  -- stream, including this independently expected sentinel, still undergoes
  -- exact state parity; unsatisfiable generated cases are never discarded.
  (actual, metrics) <- compareAll (addRoot base goals 500) query
  let observed = values "Result" query actual
      rows = filter (/= completed) observed
  observed === rows ++ [completed]
  sort rows === expected
  errors actual === []
  assertTyped metrics
  classify "posting eliminates every answer" (null expected)

genExpression :: Int -> Gen Term
genExpression depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency [(5, leaf), (3, app <$> Gen.element ["plus", "minus", "mul", "div", "mod", "^"]
      <*> sequence [genExpression (depth - 1), genExpression (depth - 1)])]
  where
    leaf = Gen.element [IntLit (-2), IntLit 0, IntLit 2, FloatLit 1.5, Var 37,
      Atom "bad", app "bad_expression" [Var 499]]

prop_generated_errors_match_full_ordered_branch_state :: Property
prop_generated_errors_match_full_ordered_branch_state = withTests 150 . property $ do
  left <- forAll (genExpression 2)
  right <- forAll (genExpression 2)
  name <- forAll (Gen.element ["is", "gt", "lt", "gte", "lte", "equiv", "neq"])
  base <- rootBase
  let target = if name == "is" then Var 0 else left
      goal = app name [target, right]
      program = addRoot base [unify (Var 499) (Atom "seed"),
        app ";" [app "," [goal, unify (Var 0) (Atom "accepted")], unify (Var 0) (Atom "fallback")]] 500
  (_, metrics) <- compareAll program rootQuery
  assertTyped metrics

prop_arithmetic_error_priority_and_scalar_ordering :: Property
prop_arithmetic_error_priority_and_scalar_ordering = unit $ do
  base <- rootBase
  let zero = app "div" [IntLit 1, IntLit 0]
      scenarios =
        [ (app "gt" [Var 1, Atom "right_bad"], [ExpectedNumber (Atom "right_bad")]),
          (app "gt" [Atom "left_bad", zero], [ExpectedNumber (Atom "left_bad")]),
          (app "gt" [zero, Atom "right_bad"], [DivisionByZero]),
          (app "gt" [Var 1, Var 2], [InstantiationError (Var 2)]),
          (app "is" [Var 0, app "plus" [Var 1, Atom "right_bad"]], [ExpectedNumber (Atom "right_bad")]),
          (app "is" [Var 0, app "div" [Var 1, IntLit 0]], [DivisionByZero]),
          (app "is" [Var 0, app "mod" [IntLit 4, FloatLit 1.5]], [ExpectedInteger (FloatLit 1.5)]),
          (app "is" [Var 0, app "^" [IntLit 2, IntLit (-1)]], [NegativeIntegerExponent (-1)]),
          (app "is" [Atom "bad_target", zero], [DivisionByZero]),
          (app "gt" [Atom "z", Atom "a"], []),
          (app "lt" [CharLit 'a', CharLit 'z'], []),
          (app "gte" [StrLit "z", StrLit "a"], [])
        ]
  forM_ scenarios $ \(goal, expected) -> do
    annotateShow goal
    let program = addRoot base [goal] 3
    (actual, metrics) <- compareAll program rootQuery
    errors actual === expected
    assertTyped metrics
    assertTraceParity program rootQuery

prop_clp_failures_aliases_output_and_opaque_retries :: Property
prop_clp_failures_aliases_output_and_opaque_retries = unit $ do
  program <- load $ unlines
    [ "<- notable.", "root : nondet unsafe (any: <=>).",
      "root Result <- X = Y, [X, Y] in 1..3,",
      "  (once (X = bad ; X = 2), write lost, fail ;",
      "   (X #= 1, Y #= 2 -> Result = impossible ; true),",
      "   not (X #> 3), findall (pair X Y) (label [X, Y]) Result, write kept)."
    ]
  (actual, metrics) <- compareAll program rootQuery
  assertTyped metrics
  values "Result" rootQuery actual === [list [app "pair" [IntLit n, IntLit n] | n <- [1 .. 3]]]
  errors actual === [CLPTypeError (Atom "bad")]
  [Reference.answerOutput (Reference.projectAnswer rootQuery state) | Reference.Found state <- actual]
    === [[Reference.WriteEvent "kept"]]
  assertTraceParity program rootQuery

prop_fallback_arities_builtin_precedence_dynamic_and_tables :: Property
prop_fallback_arities_builtin_precedence_dynamic_and_tables = unit $ do
  base <- load $ unlines
    [ "<- notable.", "root : nondet unsafe (any: <=>).", "memo : dynamic.",
      "cached : table nondet (int: <=>).", "cached 1.", "cached 2."
    ]
  let collisions =
        [ Clause (app "gt" [Var 0, Var 1]) [Atom "fail"] 2,
          Clause (app "all_different" [Var 0]) [Atom "fail"] 1,
          Clause (app "is" [Var 0]) [unify (Var 0) (Atom "user_arity")] 1,
          Clause (app "fd_le" [Var 0, Var 1, Var 2]) [unify (Var 2) (Atom "user_three")] 3
        ]
      program = foldr addClause base collisions
      fixtures =
        [ [app "gt" [IntLit 2, IntLit 1], app "all_different" [list [IntLit 1, IntLit 2]],
            unify (Var 0) (Atom "builtin_wins")],
          [app "is" [Var 0]],
          [app "fd_le" [IntLit 2, IntLit 1, Var 0]],
          [app "fd_ne" [IntLit 1]],
          [unify (Var 1) (app "gt" [IntLit 2, IntLit 1]), Var 1, unify (Var 0) (Atom "indirect")],
          [app "assert" [app "memo" [IntLit 2]], app "memo" [Var 1],
            app "is" [Var 0, app "plus" [Var 1, IntLit 1]]],
          [app "cached" [Var 1], app "is" [Var 0, app "mul" [Var 1, IntLit 2]]]
        ]
  forM_ fixtures $ \goals -> do
    annotateShow goals
    let current = addRoot program goals 3
    _ <- compareAll current rootQuery
    assertTraceParity current rootQuery
  (_, malformedMetrics) <- compareAll (addRoot program [app "fd_ne" [IntLit 1]] 1) rootQuery
  Machine.metricTypedBuiltinCalls malformedMetrics === 0
  Machine.metricBuiltinWrappersAvoided malformedMetrics === 0
  -- Builtin precedence also survives declarations that would route an
  -- ordinary predicate through dynamic facts or a table. Declaration flags
  -- must never turn a statically recognized builtin into a predicate call.
  forM_ [FlagDynamic, FlagTable] $ \flag -> do
    let declared = addDecl (Decl "gt" (Just Nondet) [flag]
          [ArgSpec SAny ModeInOut, ArgSpec SAny ModeInOut]) program
        current = addRoot declared [app "gt" [IntLit 2, IntLit 1], unify (Var 0) (Atom "builtin_wins")] 1
    (actual, metrics) <- compareAll current rootQuery
    values "Result" rootQuery actual === [Atom "builtin_wins"]
    errors actual === []
    assertTyped metrics

operandPlan :: [Term] -> Int -> Maybe OperandPlan
operandPlan arguments count = do
  code <- compileClause (Clause (Atom "root") [app "unify" arguments] count)
  case codeControls code of
    [control] -> case controlView control of
      BuiltinCall BuiltinUnify plan _ -> Just plan
      _ -> Nothing
    _ -> Nothing

genData :: Int -> Gen Term
genData depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency [(4, leaf), (3, app <$> Gen.element ["pair", "box", "node"]
      <*> Gen.list (Range.linear 0 3) (genData (depth - 1)))]
  where
    leaf = Gen.element [Var 0, Var 3, Var 7, Var 13, Var 37, Var 499, IntLit 2, Atom "!", Atom "same",
      StrLit "same", CharLit 'a', FloatLit (-0.0), FloatLit 0,
      FloatLit (castWord64ToDouble 0x7ff8000000000042)]

data OperandObservation = OperandObservation [Term] [Term] Store [VarId]
  deriving (Eq, Show)

observeOperands :: Heap.Heap s -> Bridge.Bindings -> Store -> [Heap.Address] -> ST s OperandObservation
observeOperands heap bindings store roots = do
  raw <- must (Bridge.exportRawTerms heap bindings roots)
  walked <- must (Bridge.exportTerms heap bindings roots)
  pure (OperandObservation (map bits raw) (map bits walked) (storeBits store) (Bridge.bindingVariables bindings))

prop_generated_multi_root_operands_match_source_import_and_frozen_replay :: Property
prop_generated_multi_root_operands_match_source_import_and_frozen_replay = withTests 200 . property $ do
  left <- forAll (genData 3)
  right <- forAll (genData 3)
  alias <- forAll Gen.bool
  base <- forAll (Gen.int (Range.linear 1000 2000))
  let arguments = [left, right]
      ids = IS.toAscList (IS.fromList (concatMap termVarIds arguments))
      globals = map (+ base) ids
      aliases = case globals of
        first : rest | alias -> case reverse rest of
          final : _ -> IM.singleton first (Var final)
          [] -> IM.empty
        _ -> IM.empty
      store = emptyStore {stSubst = aliases}
  plan <- evalMaybe (operandPlan arguments 500)
  operandLocalIds plan === ids
  operandLocalCount plan === length ids
  operandVariables plan === IS.fromList ids
  length (operandRuntimeRoots plan) === 2
  let result = runST $ do
        original <- Heap.newHeap
        bindings <- must (Bridge.newBindings original (0 : globals))
        ready <- must (Bridge.syncState original bindings ((Reference.initialState 0) {Reference.ssStore = store}))
        frozen <- Heap.freezeHeap original
        before <- Heap.heapSize original
        let run measured = do
              heap <- Heap.thawHeap frozen
              step <- must ((if measured then Bytecode.materializeOperandsMeasured else Bytecode.materializeOperands)
                heap ready base plan)
              observed <- observeOperands heap ready store (Bytecode.operandStepRoots step)
              pure (observed, (Bytecode.operandStepAllocationInstructions step, Bytecode.operandStepRegisterSlots step))
        (normal, counters) <- run False
        (counted, measuredCounters) <- run True
        (replay, _) <- run False
        legacy <- Heap.thawHeap frozen
        (imported, roots) <- must (Bridge.importTerms legacy ready (map (Unify.renameBody base) arguments))
        expected <- observeOperands legacy imported store roots
        after <- Heap.heapSize original
        pure (normal, counted, replay, expected, counters, measuredCounters, before == after)
  case result of
    (normal, counted, replay, expected, counters, measuredCounters, untouched) -> do
      normal === expected
      counted === expected
      replay === expected
      counters === (0, 0)
      fst measuredCounters === length (operandRuntimeInstructions plan)
      assert (snd measuredCounters <= operandRegisterCount plan)
      assert untouched

prop_multi_root_shared_temporaries_strict_roots_and_atomic_failure :: Property
prop_multi_root_shared_temporaries_strict_roots_and_atomic_failure = unit $ do
  let shared = app "pair" [Var 37, app "box" [Atom "!", Var 499]]
      arguments = [app "outer" [shared, Var 0], shared]
  plan <- evalMaybe (operandPlan arguments 500)
  scalar <- evalMaybe (operandPlan [IntLit 1, IntLit 2] 0)
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0, 100, 137, 599])
        step <- must (Bytecode.materializeOperandsMeasured heap bindings 100 plan)
        raw <- must (Bridge.exportRawTerms heap bindings (Bytecode.operandStepRoots step))
        prefix <- Heap.freezeHeap heap
        (stale, _) <- must (Bridge.importTerms heap bindings [Var 999])
        Heap.restoreHeap heap prefix
        let stats = (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        before <- stats
        rejected <- Bytecode.materializeOperands heap stale 100 scalar
        rejectedMeasured <- Bytecode.materializeOperandsMeasured heap stale 100 scalar
        after <- stats
        (retired, live, _, _) <- must (Bridge.rebuild heap bindings [0, 100] (Reference.initialState 0) [])
        missingBefore <- (,,) <$> Heap.heapSize retired <*> Heap.trailSize retired <*> Heap.internSize retired
        missing <- Bytecode.materializeOperandsMeasured retired live 100 plan
        missingAfter <- (,,) <$> Heap.heapSize retired <*> Heap.trailSize retired <*> Heap.internSize retired
        pure (raw, case rejected of Left (Heap.InvalidAddress _) -> True; _ -> False,
          case rejectedMeasured of Left (Heap.InvalidAddress _) -> True; _ -> False,
          before == after, case missing of Left Heap.IncompatibleBindings -> True; _ -> False,
          missingBefore == missingAfter, Bridge.bindingVariables live)
  case result of
    (raw, rejected, rejectedMeasured, atomic, missing, atomicMissing, live) -> do
      map bits raw === map (bits . Unify.renameBody 100) arguments
      assert rejected
      assert rejectedMeasured
      assert atomic
      assert missing
      assert atomicMissing
      live === [0, 100]

prop_interleaved_typed_checkpoints_keep_retained_results_and_traces :: Property
prop_interleaved_typed_checkpoints_keep_retained_results_and_traces = unit $ do
  program <- load $ unlines
    [ "<- notable.", "root : nondet unsafe (any: <=>).",
      "root Result <- [X, Y] in 1..3, X #< Y,",
      "  once (X #>= 1), (X #= 1 -> true ; Y #= 3),",
      "  label [X, Y], N is X * 10 + Y, write N, Result = pair N X."
    ]
  first <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program rootQuery)
  independent <- evalEither (Machine.startWithBackend Machine.Bytecode program rootQuery)
  step <- evalEither (Machine.resume first)
  case step of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = events rootQuery [retained]
      _ <- evalIO (evaluate (length (show before)))
      (allIndependent, _) <- evalEither (drain independent)
      (rest, metrics) <- evalEither (drain next)
      (again, repeatedMetrics) <- evalEither (drain next)
      (allAgain, _) <- evalEither (drain first)
      before === events rootQuery [retained]
      events rootQuery rest === events rootQuery again
      metrics === repeatedMetrics
      before ++ events rootQuery rest === events rootQuery allAgain
      events rootQuery allAgain === events rootQuery allIndependent
      events rootQuery allAgain === events rootQuery (Reference.solveQuery program rootQuery)
      assertTyped metrics
  assertTraceParity program rootQuery

machineTypedBuiltinGroup :: Group
machineTypedBuiltinGroup = Group "typed builtin operands"
  [ ("generated arithmetic sparse aliases and controls match independent results", prop_generated_arithmetic_sparse_aliases_and_controls)
  , ("generated CLP posting matches a finite independent model", prop_generated_clp_posting_and_independent_finite_model)
  , ("generated malformed arithmetic preserves ordered complete branch state", prop_generated_errors_match_full_ordered_branch_state)
  , ("arithmetic error priority and scalar comparisons remain exact", prop_arithmetic_error_priority_and_scalar_ordering)
  , ("CLP errors aliases output and opaque retries roll back together", prop_clp_failures_aliases_output_and_opaque_retries)
  , ("fallback arities builtin precedence dynamic facts and tables remain compatible", prop_fallback_arities_builtin_precedence_dynamic_and_tables)
  , ("generated multi root operands match source import and frozen replay", prop_generated_multi_root_operands_match_source_import_and_frozen_replay)
  , ("multi root temporaries validate strict roots and atomic failure", prop_multi_root_shared_temporaries_strict_roots_and_atomic_failure)
  , ("interleaved typed checkpoints retain independent results and traces", prop_interleaved_typed_checkpoints_keep_retained_results_and_traces)
  ]
