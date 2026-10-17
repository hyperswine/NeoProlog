{-# LANGUAGE OverloadedStrings #-}

-- Dense operand slots are an execution layout, never logical variable IDs.
-- Decode both public plans independently and compare their heap observations
-- with source import, including sparse locals, aliases and frozen branches.
module MachineOperandTest (machineOperandGroup) where

import Control.Monad (foldM, forM_)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
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
import qualified Infera.Machine.CLP as NativeCLP
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program (Program, addClause)
import Infera.Syntax
import qualified Infera.Unify as Unify

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

must :: Show problem => ST s (Either problem value) -> ST s value
must action = action >>= either (error . show) pure

bits :: Term -> Term
bits (FloatLit number) = Compound "$operand_float_bits" [IntLit (fromIntegral (castDoubleToWord64 number))]
bits (Compound name arguments) = Compound name (map bits arguments)
bits term = term

storeBits :: Store -> Store
storeBits store = store
  {stSubst = IM.map bits (stSubst store), stConstraints = map constraintBits (stConstraints store),
   stConstraintMap = IM.map constraintBits (stConstraintMap store)}
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
    combined = Compound "$operand_roots" (names ++ terms)

type TableMetadata = Map.Map Term (Bool, Bool, [(Term, Int, [Reference.OutputEvent])], Set.Set Term)

tableMetadata :: Reference.SolverState -> TableMetadata
tableMetadata = Map.mapKeys bits . Map.map entry . Reference.ssTables
  where
    entry table = (Reference.teComplete table, Reference.teTruncated table,
      [(bits term, count, output) | (term, count, output) <- Reference.teAnswers table], Set.map bits (Reference.teSet table))

data Event
  = Answer [(String, Term)] [String] [Reference.OutputEvent] Store Int Int TableMetadata (Map.Map PredKey [(Term, Int)])
  | Error SolveError | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

events :: Query -> Reference.Search -> [Event]
events query = map event
  where
    normalize term = case canonical query [term] of [value] -> value; _ -> error "canonical root count"
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
            metadata = storeBits ((Reference.ssStore state) {stSubst = Unify.emptySubst})
            dynamic = Map.map (map (\(term, count) -> (bits term, count))) (Reference.ssDynamic state)
         in Answer (zip (map fst bindings) (canonical query (map snd bindings)))
              (Reference.answerResiduals answer) (Reference.answerOutput answer) metadata
              (Reference.ssFresh state) (Reference.ssOutLen state) (tableMetadata state) dynamic
      Reference.BranchError problem -> Error (errorTerms normalize problem)
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

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

planFor :: Term -> Int -> Maybe DataPlan
planFor term count = do
  code <- compileClause (Clause (Atom "root") [term] count)
  case codeControls code of
    [control] -> case controlView control of
      Invoke plan _ -> Just plan
      BuiltinCall _ _ fallback -> Just fallback
      _ -> Nothing
    _ -> Nothing

-- Both decoders capture every child value before overwriting a physical
-- destination. Dense locals are resolved through the separate source-ID list.
decodeDense :: VarId -> DataPlan -> Either String (Term, Bool)
decodeDense base plan = do
  (registers, reused) <- foldM instruction (IM.empty, False) (dataRuntimeInstructions plan)
  root <- operand registers (dataRuntimeRoot plan)
  pure (root, reused)
  where
    ids = dataLocalIds plan
    valid register = register >= 0 && register < dataRegisterCount plan
    operand _ (DataLocal local)
      | local >= 0 && local < length ids = Right (Var (base + ids !! local))
      | otherwise = Left "dense local outside source-ID table"
    operand registers (DataTemporary register) = maybe (Left "uninitialized dense temporary") Right (IM.lookup register registers)
    instruction (registers, reused) operation = do
      (destination, value, overwritesChild) <- case operation of
        DataConstant destination scalar -> case scalar of
          Var _ -> Left "dense constant contains a local"
          Compound _ _ -> Left "dense constant contains a constructor"
          _ -> Right (destination, scalar, False)
        DataOwner destination -> Right (destination, IntLit (toInteger base), False)
        DataCompound destination name children -> do
          arguments <- mapM (operand registers) children
          pure (destination, Compound name arguments, DataTemporary destination `elem` children)
      if valid destination then Right (IM.insert destination value registers, reused || overwritesChild)
        else Left "dense destination outside temporary array"

decodeLegacy :: VarId -> DataPlan -> Either String Term
decodeLegacy base plan = do
  registers <- foldM instruction IM.empty (dataInstructions plan)
  operand registers (dataRoot plan)
  where
    operand _ (Local local) = Right (Var (base + local))
    operand registers (Temporary register) = maybe (Left "uninitialized legacy temporary") Right (IM.lookup register registers)
    instruction registers operation = do
      (destination, value) <- case operation of
        GoalConstant destination scalar -> pure (destination, scalar)
        GoalOwner destination -> pure (destination, IntLit (toInteger base))
        GoalCompound destination name children -> do
          arguments <- mapM (operand registers) children
          pure (destination, Compound name arguments)
      if destination >= 0 && destination < dataRegisterCount plan then pure (IM.insert destination value registers)
        else Left "legacy destination outside temporary array"

allocatedSlots :: DataPlan -> Int
allocatedSlots plan = case (dataRuntimeInstructions plan, dataRuntimeRoot plan) of
  ([], DataLocal _) -> 0
  ([DataConstant destination _], DataTemporary root) | destination == root -> 0
  ([DataOwner destination], DataTemporary root) | destination == root -> 0
  ([DataCompound destination _ children], DataTemporary root)
    | destination == root && all local children -> 0
  _ -> dataRegisterCount plan
  where local (DataLocal _) = True; local _ = False

genScalar :: Gen Term
genScalar = Gen.choice
  [Atom <$> Gen.element ["a", "same", "!", "\955"], IntLit <$> Gen.integral (Range.linear (-3) 3),
   FloatLit <$> Gen.element [-0.0, 0.0, 1.5, castWord64ToDouble 0x7ff8000000000042,
     castWord64ToDouble 0x7ff8000000000043],
   CharLit <$> Gen.element ['a', '\955'], StrLit <$> Gen.element ["", "same", "\955"]]

genTerm :: [Int] -> Int -> Gen Term
genTerm locals depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency [(4, leaf), (3, Compound <$> Gen.element ["box", "pair", "same"]
      <*> Gen.list (Range.linear 0 3) (genTerm locals (depth - 1)))]
  where
    leaf | null locals = genScalar
         | otherwise = Gen.frequency [(3, genScalar), (2, Var <$> Gen.element locals)]

data Scenario = Scenario Term VarId Store [VarId]
  deriving Show

genScenario :: Gen Scenario
genScenario = do
  locals <- Gen.subsequence [0, 3, 7, 13, 31]
  original <- genTerm locals 3
  base <- Gen.int (Range.linear 100 1000)
  alias <- Gen.int (Range.linear 0 2)
  constrained <- Gen.bool
  let term = case original of Atom "!" -> Compound "box" [original]; _ -> original
      used = IS.toAscList (IS.fromList (termVarIds term))
      absolute = map (+ base) used
      aliases = case absolute of
        first : rest | not (null rest) -> case alias of
          1 -> IM.singleton first (Var (last rest))
          2 -> IM.singleton (last rest) (Var first)
          _ -> IM.empty
        _ -> IM.empty
      initial = emptyStore {stSubst = aliases}
      bounded = case absolute of
        first : _ | constrained -> addDomains [Var first] (Fin (-2)) (Fin 2) initial
        _ -> Right (Just initial)
  case bounded of
    Right (Just store) -> pure (Scenario term base store (0 : base + 65 : absolute))
    _ -> error "generated domains unexpectedly rejected"

data Observation = Observation Store [Term] [Term] [VarId]
  deriving (Eq, Show)

observeRoot :: Heap.Heap s -> Bridge.Bindings -> Store -> Heap.Address -> ST s Observation
observeRoot heap bindings store root = do
  raw <- must (Bridge.exportRawTerms heap bindings [root])
  values <- must (Bridge.exportTerms heap bindings [root])
  pure (Observation (storeBits store) (map bits raw) (map bits values) (Bridge.bindingVariables bindings))

bindFirst :: Heap.Heap s -> Bridge.Bindings -> Store -> [VarId] -> ST s (Bridge.Bindings, Store)
bindFirst _ bindings store [] = pure (bindings, store)
bindFirst heap bindings store (variable : _) = do
  result <- must (NativeCLP.bindInteger heap bindings store variable 1)
  case result of Right (Just accepted) -> pure accepted; _ -> error "generated integer binding rejected"

compareMaterialization :: Scenario -> DataPlan
  -> ((Observation, Observation), (Observation, Observation), (Observation, Observation),
      (Observation, Observation), (Int, Int), (Int, Int), Bool)
compareMaterialization (Scenario term base store ids) plan = runST $ do
  original <- Heap.newHeap
  bindings <- must (Bridge.newBindings original ids)
  ready <- must (Bridge.syncState original bindings ((Reference.initialState 0) {Reference.ssStore = store}))
  frozen <- Heap.freezeHeap original
  size <- Heap.heapSize original
  let used = map (+ base) (IS.toAscList (IS.fromList (termVarIds term)))
      execute measured heap = do
        step <- must ((if measured then Bytecode.materializeDataMeasured else Bytecode.materializeData) heap ready base plan)
        before <- observeRoot heap ready store (Bytecode.dataStepRoot step)
        (updated, nextStore) <- bindFirst heap ready store used
        after <- observeRoot heap updated nextStore (Bytecode.dataStepRoot step)
        pure ((before, after), (Bytecode.dataStepAllocationInstructions step, Bytecode.dataStepRegisterSlots step))
  native <- Heap.thawHeap frozen
  (actual, counters) <- execute False native
  measured <- Heap.thawHeap frozen
  (counted, measuredCounters) <- execute True measured
  repeated <- Heap.thawHeap frozen
  (replay, _) <- execute False repeated
  legacy <- Heap.thawHeap frozen
  (imported, roots) <- must (Bridge.importTerms legacy ready [Unify.renameBody base term])
  root <- case roots of [one] -> pure one; _ -> error "legacy root count changed"
  before <- observeRoot legacy imported store root
  (updated, nextStore) <- bindFirst legacy imported store used
  after <- observeRoot legacy updated nextStore root
  retainedSize <- Heap.heapSize original
  pure (actual, counted, replay, (before, after), counters, measuredCounters, size == retainedSize)

prop_generated_dense_source_legacy_and_heap_observations :: Property
prop_generated_dense_source_legacy_and_heap_observations = withTests 400 . property $ do
  scenario@(Scenario term base _ _) <- forAll genScenario
  let count = maximum (0 : map (+ 1) (termVarIds term))
  plan <- evalMaybe (planFor term count)
  dataLocalIds plan === IS.toAscList (IS.fromList (termVarIds term))
  dataLocalCount plan === length (dataLocalIds plan)
  dataVariables plan === IS.fromList (termVarIds term)
  (dense, reused) <- evalEither (decodeDense base plan)
  legacy <- evalEither (decodeLegacy base plan)
  bits dense === bits (Unify.renameBody base term)
  bits legacy === bits dense
  classify "dense local gaps" (any (> dataLocalCount plan) (dataLocalIds plan))
  classify "child destination reused" reused
  let (actual, measured, replay, expected, normalCounters, measuredCounters, untouched) = compareMaterialization scenario plan
  actual === expected
  measured === expected
  replay === expected
  normalCounters === (0, 0)
  measuredCounters === (length (dataRuntimeInstructions plan), allocatedSlots plan)
  assert untouched

prop_generated_sparse_operands_in_compiled_control_and_clp :: Property
prop_generated_sparse_operands_in_compiled_control_and_clp = withTests 200 . property $ do
  Scenario term _ _ _ <- forAll genScenario
  wrapper <- forAll (Gen.int (Range.linear 0 4))
  let shifted = Unify.renameTerm 1 term
      payload = Compound "payload" [shifted]
      count = maximum (1 : map (+ 1) (termVarIds payload))
      assign = Compound "unify" [Var 0, payload]
      (body, variables, multiplicity, expected) = case wrapper of
        1 -> (Compound "once" [assign], count, 1, payload)
        2 -> (Compound ";" [assign, assign], count, 2, payload)
        3 -> (Compound "findall" [Var count, Compound "unify" [Var count, payload], Var 0],
          count + 1, 1, mkList [payload] Nothing)
        4 -> (Compound ";" [Compound "->" [Atom "true", assign], Atom "missing"], count, 1, payload)
        _ -> (assign, count, 1, payload)
      domain = case IS.toAscList (IS.fromList (termVarIds payload)) of
        first : _ -> [Compound "in" [Var first, Compound "range" [IntLit (-2), IntLit 2]]]
        [] -> []
      clause = Clause (Compound "root" [Var 0]) (domain ++ [body]) variables
      query = Query [Compound "root" [Var 0]] [("Result", 0)] 1
  base <- load "<- notable.\nroot : nondet (any: <=>)."
  let program = addClause clause base
      reference = Reference.solveQuery program query
      interpreted = Machine.solveQueryWithBackend Machine.Interpreted program query
  normal <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  measured <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, disabled) <- evalEither (drain normal)
  (counted, metrics) <- evalEither (drain measured)
  events query actual === events query reference
  events query actual === events query interpreted
  events query counted === events query actual
  rawStores actual === rawStores reference
  rawStores actual === rawStores interpreted
  rawStores counted === rawStores actual
  let results = [value | Reference.Found state <- actual,
        Just value <- [lookup "Result" (Reference.answerBindings (Reference.projectAnswer query state))]]
  canonical query results === canonical query (replicate multiplicity (Unify.renameBody 1 expected))
  [Reference.ssFresh state | Reference.Found state <- actual] === replicate multiplicity (1 + max 1 variables)
  [problem | Reference.BranchError problem <- actual] === []
  assert (Machine.metricCompiledActivations metrics > 0)
  assert (Machine.metricBodyAllocationInstructions metrics > 0)
  disabled === Machine.checkpointMetrics normal

heapStats :: Heap.Heap s -> ST s (Int, Int, (Int, Int))
heapStats heap = (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap

bindingView :: Bridge.Bindings -> ([VarId], IS.IntSet)
bindingView bindings = (Bridge.bindingVariables bindings, Bridge.bindingVariableSet bindings)

assertBindingViews :: [([VarId], IS.IntSet)] -> PropertyT IO ()
assertBindingViews views = forM_ views $ \(variables, variableSet) ->
  variableSet === IS.fromList variables

prop_dense_gaps_repeated_locals_owner_bits_and_child_overwrite :: Property
prop_dense_gaps_repeated_locals_owner_bits_and_child_overwrite = unit $ do
  let nan1 = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      nan2 = FloatLit (castWord64ToDouble 0x7ff8000000000043)
      term = Compound "node"
        [Compound "pair" [Var 499, Compound "box" [Var 37]],
         Compound "pair" [Var 0, Var 499], Var 37,
         Compound "typed" [IntLit 1, FloatLit 1, FloatLit (-0.0), FloatLit 0.0,
           nan1, nan1, nan2, Atom "same", Compound "same" [], CharLit 'a', StrLit "a"],
         Compound "owner" [Atom "!", IntLit 100]]
      scenario = Scenario term 100 emptyStore [0, 100, 137, 599]
  plan <- evalMaybe (planFor term 500)
  dataLocalIds plan === [0, 37, 499]
  dataLocalCount plan === 3
  (decoded, reused) <- evalEither (decodeDense 100 plan)
  bits decoded === bits (Unify.renameBody 100 term)
  assert reused
  assert (dataRegisterCount plan < length (dataRuntimeInstructions plan))
  let (actual, measured, replay, expected, _, counts, intact) = compareMaterialization scenario plan
  actual === expected
  measured === expected
  replay === expected
  counts === (length (dataRuntimeInstructions plan), allocatedSlots plan)
  assert intact

prop_fast_operands_retain_raw_aliases_and_validate_stale_empty_lookups :: Property
prop_fast_operands_retain_raw_aliases_and_validate_stale_empty_lookups = unit $ do
  let nan = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      terms = [Var 37, IntLit 7, FloatLit (-0.0), nan,
        Compound "single" [Var 37, Var 37], Compound "empty" []]
  forM_ terms $ \term -> do
    plan <- evalMaybe (planFor term 38)
    let result = runST $ do
          heap <- Heap.newHeap
          bindings <- must (Bridge.newBindings heap [0, 137])
          let store = emptyStore {stSubst = IM.fromList [(0, nan), (137, Var 0)]}
          ready <- must (Bridge.syncState heap bindings ((Reference.initialState 0) {Reference.ssStore = store}))
          step <- must (Bytecode.materializeDataMeasured heap ready 100 plan)
          observed <- observeRoot heap ready store (Bytecode.dataStepRoot step)
          pure (observed, Bytecode.dataStepAllocationInstructions step, Bytecode.dataStepRegisterSlots step)
    case result of
      (Observation store raw values _, instructions, registers) -> do
        raw === [bits (Unify.renameBody 100 term)]
        values === [bits (Unify.deepWalk (IM.fromList [(0, nan), (137, Var 0)]) (Unify.renameBody 100 term))]
        store === storeBits (emptyStore {stSubst = IM.fromList [(0, nan), (137, Var 0)]})
        instructions === length (dataRuntimeInstructions plan)
        registers === 0
    let staleResult = runST $ do
          heap <- Heap.newHeap
          bindings <- must (Bridge.newBindings heap [0])
          prefix <- Heap.freezeHeap heap
          (stale, _) <- must (Bridge.importTerms heap bindings [Var 137])
          Heap.restoreHeap heap prefix
          before <- heapStats heap
          normal <- Bytecode.materializeData heap stale 100 plan
          measured <- Bytecode.materializeDataMeasured heap stale 100 plan
          after <- heapStats heap
          let invalid outcome = case outcome of Left (Heap.InvalidAddress _) -> True; _ -> False
          pure (invalid normal, invalid measured, before == after)
    staleResult === (True, True, True)

prop_collected_source_roots_are_strict_and_never_resurrected :: Property
prop_collected_source_roots_are_strict_and_never_resurrected = unit $ do
  needed <- evalMaybe (planFor (Compound "single" [Var 37, Var 499, Var 37]) 500)
  scalar <- evalMaybe (planFor (IntLit 7) 0)
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap ([0 .. 100] ++ [137, 599]))
        (imported, _) <- must (Bridge.importTerms heap bindings [Var (-7), Var 137, Var (-7)])
        frozen <- Heap.freezeHeap heap
        (collected, live, _, _) <- must (Bridge.rebuild heap imported [0, 137, 599] (Reference.initialState 0) [])
        root <- must (Bytecode.materializeDataMeasured collected live 100 needed)
        raw <- must (Bridge.exportRawTerms collected live [Bytecode.dataStepRoot root])
        before <- heapStats collected
        stale <- Bytecode.materializeData collected imported 100 scalar
        after <- heapStats collected
        (retired, sparse, _, _) <- must (Bridge.rebuild collected live [0] (Reference.initialState 0) [])
        beforeMissing <- heapStats retired
        missing <- Bytecode.materializeDataMeasured retired sparse 100 needed
        afterMissing <- heapStats retired
        retained <- Heap.thawHeap frozen
        retainedRoots <- must (Bridge.lookupVariables retained imported [599, 137, 137])
        retainedRaw <- must (Bridge.exportRawTerms retained imported retainedRoots)
        pure (map bits raw, Bytecode.dataStepRegisterSlots root, Bridge.bindingVariables live,
          case stale of Left (Heap.InvalidAddress _) -> True; _ -> False,
          before == after, case missing of Left Heap.IncompatibleBindings -> True; _ -> False,
          beforeMissing == afterMissing, Bridge.bindingVariables sparse, map bits retainedRaw,
          [bindingView bindings, bindingView imported, bindingView live, bindingView sparse, bindingView imported])
  case result of
    (raw, slots, live, stale, unchanged, missing, atomicMissing, retired, retained, views) -> do
      raw === [Compound "single" [Var 137, Var 599, Var 137]]
      slots === 0
      live === [0, 137, 599]
      assert stale
      assert unchanged
      assert missing
      assert atomicMissing
      retired === [0]
      retained === [Var 599, Var 137, Var 137]
      assertBindingViews views
      map fst views === [[0 .. 100] ++ [137, 599], (-7) : [0 .. 100] ++ [137, 599],
        [0, 137, 599], [0], (-7) : [0 .. 100] ++ [137, 599]]

prop_frozen_dense_operands_keep_independent_alias_writes :: Property
prop_frozen_dense_operands_keep_independent_alias_writes = unit $ do
  let nan = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      term = Compound "pair" [Var 37, Compound "box" [Var 499], nan]
      store = emptyStore {stSubst = IM.singleton 137 (Var 599)}
  plan <- evalMaybe (planFor term 500)
  let result = runST $ do
        original <- Heap.newHeap
        bindings <- must (Bridge.newBindings original [0, 137, 599])
        ready <- must (Bridge.syncState original bindings ((Reference.initialState 0) {Reference.ssStore = store}))
        step <- must (Bytecode.materializeData original ready 100 plan)
        prefix <- Heap.freezeHeap original
        let branch number = do
              heap <- Heap.thawHeap prefix
              bound <- must (NativeCLP.bindInteger heap ready store 137 number)
              (updated, nextStore) <- case bound of Right (Just accepted) -> pure accepted; _ -> error "fork binding rejected"
              observed <- observeRoot heap updated nextStore (Bytecode.dataStepRoot step)
              pure (observed, bindingView updated)
        (first, firstView) <- branch 1
        (second, secondView) <- branch 2
        (again, againView) <- branch 1
        retained <- observeRoot original ready store (Bytecode.dataStepRoot step)
        pure (first, second, again, retained,
          [bindingView bindings, bindingView ready, firstView, secondView, againView])
  case result of
    (first@(Observation _ raw values1 _), Observation _ raw2 values2 _, again,
      Observation originalStore originalRaw originalValue _, views) -> do
      raw === [bits (Unify.renameBody 100 term)]
      raw2 === raw
      values1 === [bits (Compound "pair" [IntLit 1, Compound "box" [IntLit 1], nan])]
      values2 === [bits (Compound "pair" [IntLit 2, Compound "box" [IntLit 2], nan])]
      first === again
      originalStore === storeBits store
      originalRaw === raw
      originalValue === [bits (Unify.deepWalk (stSubst store) (Unify.renameBody 100 term))]
      assertBindingViews views
      map fst views === replicate 5 [0, 137, 599]

prop_structured_clp_operands_cross_collection_in_normal_and_measured_execution :: Property
prop_structured_clp_operands_cross_collection_in_normal_and_measured_execution = unit $ do
  base <- load $ unlines
    [ "<- notable.", "root : nondet unsafe (any: <=>).",
      "down 0 done.", "down N Result <- N > 0, M is N - 1, down M Result."
    ]
  let domain local = Compound "in" [Var local, Compound "range" [IntLit 1, IntLit 3]]
      board = Compound "board" [mkList
        [Compound "component" [IntLit (fromIntegral index), Compound "place" [Var 37, Var 499]]
          | index <- [0 :: Int .. 383]] Nothing]
      yes = Compound "," [Compound "down" [IntLit 3000, Atom "done"],
        Compound "," [Compound "unify" [Var 0, board], Compound "label" [mkList [Var 37, Var 499] Nothing]]]
      clause = Clause (Compound "root" [Var 0])
        [domain 37, domain 499, Compound "int_eq" [Var 499, Compound "plus" [Var 37, IntLit 1]],
         Compound ";" [Compound "->" [Atom "true", yes], Atom "missing"]] 500
      program = addClause clause base
      query = Query [Compound "root" [Var 0]] [("Board", 0)] 1
  normal <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  measured <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, disabled) <- evalEither (drain normal)
  (counted, metrics) <- evalEither (drain measured)
  events query actual === events query counted
  events query actual === events query (Reference.solveQuery program query)
  events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
  let boards = [value | Reference.Found state <- actual,
        Just value <- [lookup "Board" (Reference.answerBindings (Reference.projectAnswer query state))]]
      component entry = case entry of
        Compound "component" [IntLit identifier, Compound "place" [IntLit x, IntLit y]] -> Just (identifier, x, y)
        _ -> Nothing
      positions value = case value of
        Compound "board" [components] -> case unfoldCons components of
          (entries, Nothing) -> traverse component entries
          _ -> Nothing
        _ -> Nothing
  map positions boards === [Just [(fromIntegral index, x, y) | index <- [0 :: Int .. 383]] | (x, y) <- [(1, 2), (2, 3)]]
  [problem | Reference.BranchError problem <- actual] === []
  disabled === Machine.checkpointMetrics normal
  assert (Machine.metricCompiledActivations metrics > 0)
  assert (Machine.metricCompiledControlInstructions metrics > 0)
  assert (Machine.metricCollections metrics > 0)
  assert (Machine.metricTailCalls metrics >= 2500)
  assert (Machine.metricMaxHeapCells metrics > 1024)

prop_trusted_node_builders_preserve_caller_rollback_and_public_atomicity :: Property
prop_trusted_node_builders_preserve_caller_rollback_and_public_atomicity = unit $ do
  let nan1 = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      nan2 = FloatLit (castWord64ToDouble 0x7ff8000000000043)
      scalars = [nan1, nan2, FloatLit (-0.0), FloatLit 0.0, IntLit (2 ^ (80 :: Int)),
        Atom "same", CharLit 'a', StrLit "a"]
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0])
        root <- must (Bridge.lookupVariables heap bindings [0]) >>= \roots ->
          case roots of [one] -> pure one; _ -> error "root lookup count"
        before <- heapStats heap
        mark <- Heap.checkpoint heap
        addresses <- mapM (must . Heap.importScalarInTransaction heap) scalars
        firstAddress <- case addresses of
          first : _ -> pure first
          [] -> error "scalar fixture unexpectedly empty"
        compound <- must (Heap.newCompoundInTransaction heap "transient_nodes" addresses)
        accepted <- must (Heap.unify heap root compound)
        values <- must (Heap.exportTerms heap [compound])
        (extended, _) <- must (Bridge.importTerms heap bindings [Var 999])
        during <- heapStats heap
        _ <- must (Heap.rollback heap mark)
        after <- heapStats heap
        staleCompound <- Heap.viewRaw heap compound
        staleEnvironment <- Bridge.lookupVariables heap extended []
        rawRoot <- must (Bridge.exportRawTerms heap bindings [root])
        -- A later allocation may reuse the index, never the discarded handle.
        secondMark <- Heap.checkpoint heap
        replacement <- must (Heap.importScalarInTransaction heap nan1)
        staleScalar <- Heap.viewRaw heap firstAddress
        _ <- must (Heap.rollback heap secondMark)
        badVarMark <- Heap.checkpoint heap
        badVar <- Heap.importScalarInTransaction heap (Var 0)
        _ <- must (Heap.rollback heap badVarMark)
        badCompoundMark <- Heap.checkpoint heap
        badCompound <- Heap.importScalarInTransaction heap (Compound "invalid_scalar" [])
        _ <- must (Heap.rollback heap badCompoundMark)
        partialMark <- Heap.checkpoint heap
        partial <- must (Heap.importScalarInTransaction heap (StrLit "partial_allocation"))
        failed <- Heap.newCompoundInTransaction heap "uncommitted_functor" [partial, compound]
        _ <- must (Heap.rollback heap partialMark)
        afterPartial <- heapStats heap
        stalePartial <- Heap.viewRaw heap partial
        publicBefore <- heapStats heap
        publicFailure <- Heap.newCompound heap "public_failure" [compound]
        publicAfter <- heapStats heap
        -- The general public importer still accepts variables/constructors.
        publicMark <- Heap.checkpoint heap
        variable <- must (Heap.importTerm heap (Var 5))
        variableShape <- must (Heap.viewRaw heap variable)
        ordinary <- must (Heap.importTerm heap (Compound "public_constructor" [IntLit 7]))
        ordinaryValue <- must (Heap.exportTerms heap [ordinary])
        _ <- must (Heap.rollback heap publicMark)
        final <- heapStats heap
        let invalid outcome = case outcome of Left (Heap.InvalidAddress _) -> True; _ -> False
            incompatible outcome = case outcome of Left Heap.IncompatibleBindings -> True; _ -> False
        pure (accepted, map bits values, before, during, after, invalid staleCompound,
          invalid staleEnvironment, rawRoot, replacement /= firstAddress, invalid staleScalar,
          incompatible badVar, incompatible badCompound, invalid failed, invalid stalePartial,
          afterPartial, invalid publicFailure, publicBefore == publicAfter,
          case variableShape of Heap.VariableView original -> original == variable; _ -> False,
          ordinaryValue, final)
  case result of
    (accepted, values, before, during, after, staleCompound, staleEnvironment, rawRoot, newGeneration,
      staleScalar, badVar, badCompound, failed, stalePartial, afterPartial, publicFailure,
      publicAtomic, publicVariable, publicValue, final) -> do
      assert accepted
      values === [bits (Compound "transient_nodes" scalars)]
      assert (during /= before)
      after === before
      assert staleCompound
      assert staleEnvironment
      rawRoot === [Var 0]
      assert newGeneration
      assert staleScalar
      assert badVar
      assert badCompound
      assert failed
      assert stalePartial
      afterPartial === before
      assert publicFailure
      assert publicAtomic
      assert publicVariable
      publicValue === [Compound "public_constructor" [IntLit 7]]
      final === before

machineOperandGroup :: Group
machineOperandGroup = Group "dense operand source identity and ownership"
  [ ("generated dense source legacy and heap observations", prop_generated_dense_source_legacy_and_heap_observations),
    ("generated sparse operands in compiled control and CLP", prop_generated_sparse_operands_in_compiled_control_and_clp),
    ("dense gaps repeated locals owner bits and child overwrite", prop_dense_gaps_repeated_locals_owner_bits_and_child_overwrite),
    ("fast operands preserve aliases and strict stale empty lookups", prop_fast_operands_retain_raw_aliases_and_validate_stale_empty_lookups),
    ("collected source roots are strict and never resurrected", prop_collected_source_roots_are_strict_and_never_resurrected),
    ("frozen dense operands retain independent alias writes", prop_frozen_dense_operands_keep_independent_alias_writes),
    ("structured CLP operands cross collection in normal and measured execution", prop_structured_clp_operands_cross_collection_in_normal_and_measured_execution),
    ("trusted node builders preserve caller rollback and public atomicity", prop_trusted_node_builders_preserve_caller_rollback_and_public_atomicity)
  ]
