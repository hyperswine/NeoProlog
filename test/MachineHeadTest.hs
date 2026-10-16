{-# LANGUAGE OverloadedStrings #-}

-- Specialized matching must preserve the legacy head transaction: finish all
-- structural unification before propagating CLP, then allocate the body only
-- for an accepted head. Raw logical IDs and scalar bits remain observable.
module MachineHeadTest (machineHeadGroup) where

import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP
import Infera.Compile (ClauseCode, codeSlotCount, codeUnsharedSlotCount, compileClause)
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.Bytecode as Bytecode
import qualified Infera.Machine.CLP as NativeCLP
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax
import qualified Infera.Unify as Unify

data Observed
  = OAtom String | OVar VarId | OInt Integer | OFloat Word64
  | OChar Char | OString String | OCompound String [Observed]
  deriving (Eq, Show)

observe :: Term -> Observed
observe term = case term of
  Atom value -> OAtom value
  Var value -> OVar value
  IntLit value -> OInt value
  FloatLit value -> OFloat (castDoubleToWord64 value)
  CharLit value -> OChar value
  StrLit value -> OString value
  Compound name arguments -> OCompound name (map observe arguments)

bits :: Term -> Term
bits (FloatLit value) = Compound "$head_test_float_bits" [IntLit (fromIntegral (castDoubleToWord64 value))]
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

data Outcome
  = Rejected
  | Raised SolveError
  | Accepted Store [Observed] [Observed] [Observed] [VarId]
  deriving (Eq, Show)

data Scenario = Scenario Clause Term Int Store [VarId]
  deriving Show

must :: Show problem => ST s (Either problem value) -> ST s value
must action = action >>= either (error . show) pure

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["nil", "leaf", "a", "b", "\955"],
    IntLit <$> Gen.choice [Gen.integral (Range.linear (-4) 4), pure (2 ^ (80 :: Int) + 9)],
    FloatLit <$> Gen.element [-2.5, -0.0, 0.0, 1.5, -1 / 0, 1 / 0,
      castWord64ToDouble 0x7ff8000000000042],
    CharLit <$> Gen.element ['a', '\955', '\0'],
    StrLit <$> Gen.element ["", "kept", "\955", "\0"]
  ]

genTerm :: Int -> Int -> Gen Term
genTerm variables depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency
      [(4, leaf),
       (3, Compound <$> Gen.element ["box", "pair", "cons", "plus", "same"]
         <*> Gen.list (Range.linear 0 3) (genTerm variables (depth - 1)))]
  where
    leaf
      | variables <= 0 = genScalar
      | otherwise = Gen.frequency [(3, genScalar), (2, Var <$> Gen.int (Range.linear 0 (variables - 1)))]

genScenario :: Gen Scenario
genScenario = do
  count <- Gen.int (Range.linear 0 5)
  fields <- Gen.list (Range.singleton 2) (genTerm count 2)
  body <- Gen.list (Range.linear 0 4) $ Compound "body_only"
    <$> Gen.list (Range.linear 0 3) (genTerm count 2)
  base <- Gen.int (Range.linear 10 1000)
  goalKind <- Gen.int (Range.linear 0 2)
  randomFields <- Gen.list (Range.singleton 2) (genTerm 3 2)
  aliasKind <- Gen.int (Range.linear 0 2)
  overlap <- Gen.bool
  constrained <- Gen.bool
  let mapCaller (Var variable) = Var (variable `mod` 3)
      mapCaller (Compound name arguments) = Compound name (map mapCaller arguments)
      mapCaller term = term
      goal = Compound "p" $ case goalKind of
        0 -> map mapCaller fields
        1 -> [Var 0, Var 1]
        _ -> randomFields
      aliases = case aliasKind of
        0 -> IM.empty
        1 -> IM.singleton 0 (Var 2)
        _ -> IM.singleton 2 (Var 0)
      substitution = if overlap then IM.insert base (Var 1) aliases else aliases
      initial = emptyStore {stSubst = substitution}
      bounded = if constrained then addDomains [Var 0, Var 1] (Fin (-2)) (Fin 2) initial
        else Right (Just initial)
  case bounded of
    Right (Just store) -> pure (Scenario (Clause (Compound "p" fields) body count)
      goal base store [0, 1, 2, base + max 1 count + 100])
    _ -> error "generated initial domains unexpectedly rejected"

prepare :: Heap.Heap s -> Scenario -> ST s (Bridge.Bindings, Heap.Address)
prepare heap (Scenario _ goal _ store protected) = do
  bindings <- must (Bridge.newBindings heap protected)
  ready <- must (Bridge.syncState heap bindings ((Reference.initialState 0) {Reference.ssStore = store}))
  (imported, roots) <- must (Bridge.importTerms heap ready [goal])
  case roots of
    [root] -> pure (imported, root)
    _ -> error "goal import changed root count"

accepted :: Heap.Heap s -> Bridge.Bindings -> Store -> Heap.Address -> [Heap.Address]
  -> ST s Outcome
accepted heap bindings store goal body = do
  goalValue <- must (Bridge.exportTerms heap bindings [goal])
  raw <- must (Bridge.exportRawTerms heap bindings body)
  values <- must (Bridge.exportTerms heap bindings body)
  pure (Accepted (storeBits store) (map observe goalValue) (map observe raw)
    (map observe values) (Bridge.bindingVariables bindings))

-- This deliberately keeps the published legacy implementation as the oracle:
-- rename/import the complete head and body, then one native CLP unification.
legacy :: Heap.Heap s -> Bridge.Bindings -> Heap.Address -> Scenario -> ST s Outcome
legacy heap bindings goal (Scenario clause _ base store _) = do
  let count = max 1 (clauseNVars clause)
      headTerm = Unify.renameTerm base (clauseHead clause)
      body = map (Unify.renameBody base) (clauseBody clause)
  (ready, roots) <- must (Bridge.importTerms heap bindings
    (map Var [base .. base + count - 1] ++ headTerm : body))
  case drop count roots of
    headRoot : bodyRoots -> do
      outcome <- must (NativeCLP.unify heap ready store goal headRoot)
      case outcome of
        Left problem -> pure (Raised (errorBits problem))
        Right Nothing -> pure Rejected
        Right (Just (matched, nextStore)) -> accepted heap matched nextStore goal bodyRoots
    _ -> error "legacy activation changed root count"

specialized :: Heap.Heap s -> Bridge.Bindings -> Heap.Address -> Scenario -> ClauseCode
  -> ST s (Outcome, Maybe (Int, Int, Int, Int))
specialized heap bindings goal (Scenario _ _ base store _) code = do
  outcome <- must (Bytecode.activateMeasured heap bindings store goal base code)
  case outcome of
    Left problem -> pure (Raised (errorBits problem), Nothing)
    Right Nothing -> pure (Rejected, Nothing)
    Right (Just activation) -> do
      result <- accepted heap (Bytecode.activationBindings activation)
        (Bytecode.activationStore activation) goal (Bytecode.activationBodyRoots activation)
      pure (result, Just (Bytecode.activationHeadInstructions activation,
        Bytecode.activationAllocationInstructions activation,
        Bytecode.activationHeadCellsAvoided activation,
        Bytecode.activationRegisterSlots activation))

heapStats :: Heap.Heap s -> ST s (Int, Int, (Int, Int))
heapStats heap = (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap

compareScenario :: Scenario -> ClauseCode -> (Outcome, Outcome, Bool, Maybe (Int, Int, Int, Int))
compareScenario scenario code = runST $ do
  original <- Heap.newHeap
  (bindings, goal) <- prepare original scenario
  frozen <- Heap.freezeHeap original
  before <- heapStats original
  originalValue <- must (Bridge.exportTerms original bindings [goal])
  compiled <- Heap.thawHeap frozen
  (actual, counters) <- specialized compiled bindings goal scenario code
  after <- heapStats compiled
  -- Accepted goals can acquire fresh free locals, whose names belong to the
  -- returned activation bindings. The old prefix is valid only after rollback.
  atomicFailure <- case actual of
    Accepted _ _ _ _ _ -> pure True
    _ -> do
      retained <- must (Bridge.exportTerms compiled bindings [goal])
      pure (before == after && map observe retained == map observe originalValue)
  interpreted <- Heap.thawHeap frozen
  expected <- legacy interpreted bindings goal scenario
  pure (actual, expected, atomicFailure, counters)

prop_generated_head_matches_legacy_transaction :: Property
prop_generated_head_matches_legacy_transaction = withTests 500 . property $ do
  scenario@(Scenario clause _ _ _ _) <- forAll genScenario
  code <- evalMaybe (compileClause clause)
  let (actual, expected, atomicFailure, counters) = compareScenario scenario code
  classify "accepted" (case actual of Accepted _ _ _ _ _ -> True; _ -> False)
  classify "structural mismatch or occurs failure" (actual == Rejected)
  classify "CLP or delayed arithmetic error" (case actual of Raised _ -> True; _ -> False)
  actual === expected
  assert atomicFailure
  case counters of
    Just (headInstructions, _, avoided, _) -> do
      assert (headInstructions > 0)
      assert (avoided > 0)
    Nothing -> pure ()

prop_known_shapes_avoid_head_and_register_allocation :: Property
prop_known_shapes_avoid_head_and_register_allocation = unit $ do
  let headTerm = Compound "p" [Compound "box" [IntLit 1], Compound "pair" [IntLit 2, IntLit 3]]
      scenario = Scenario (Clause headTerm [] 0) headTerm 10 emptyStore [0, 1]
  code <- evalMaybe (compileClause (Clause headTerm [] 0))
  let (actual, expected, atomicFailure, counters) = compareScenario scenario code
  actual === expected
  assert atomicFailure
  case (actual, counters) of
    (Accepted _ _ [] [] _, Just (instructions, allocations, avoided, registers)) -> do
      assert (instructions > 0)
      allocations === 0
      avoided === 3
      registers === 0
    _ -> failure
  -- A free argument must still construct its matching head subtree. This
  -- exercises the allocation path instead of proving only known-shape reuse.
  let freeScenario = Scenario (Clause headTerm [] 0)
        (Compound "p" [Var 0, Compound "pair" [IntLit 2, IntLit 3]]) 10 emptyStore [0, 1]
      (freeActual, freeExpected, _, freeCounters) = compareScenario freeScenario code
  freeActual === freeExpected
  case freeCounters of
    Just (_, allocations, avoided, registers) -> do
      assert (allocations > 0)
      assert (avoided > 0)
      assert (registers > 0)
    _ -> failure

prop_register_pool_preserves_repeated_variables_and_scalar_bits :: Property
prop_register_pool_preserves_repeated_variables_and_scalar_bits = unit $ do
  let nan = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      body = Compound "body_only"
        [Var 0, Var 0, IntLit 7, IntLit 7, FloatLit (-0.0), FloatLit 0.0, nan, nan,
         Atom "same", Compound "same" []]
      clause = Clause (Compound "p" [Var 0]) [body] 1
      scenario = Scenario clause (Compound "p" [Atom "accepted"]) 20 emptyStore [0]
  code <- evalMaybe (compileClause clause)
  assert (codeSlotCount code < codeUnsharedSlotCount code)
  let (actual, expected, _, counters) = compareScenario scenario code
  actual === expected
  case (actual, counters) of
    (Accepted _ _ raw values _, Just (_, allocations, avoided, registers)) -> do
      raw === [observe (Unify.renameBody 20 body)]
      values === [observe (Unify.deepWalk (IM.singleton 20 (Atom "accepted"))
        (Unify.renameBody 20 body))]
      assert (allocations > 0)
      assert (avoided > 0)
      assert (registers > 0 && registers <= codeSlotCount code)
    _ -> failure

prop_failed_head_never_allocates_body_and_is_atomic :: Property
prop_failed_head_never_allocates_body_and_is_atomic = unit $ do
  let hugeBody = Compound "only_in_body"
        [Compound ("body_constructor_" ++ show index)
          [StrLit ("body_constant_" ++ show index), Var 0] | index <- [0 :: Int .. 999]]
      clause = Clause (Compound "p" [Var 0, Atom "expected"]) [hugeBody] 1
      scenario = Scenario clause (Compound "p" [IntLit 7, Atom "different"])
        20 emptyStore [0, 1]
  code <- evalMaybe (compileClause clause)
  let (actual, expected, atomicFailure, counters) = compareScenario scenario code
  actual === Rejected
  actual === expected
  assert atomicFailure
  counters === Nothing
  -- The same guarantee holds after partial writes would cause an occurs cycle.
  let recursive = Clause (Compound "p" [Var 0, Compound "box" [Var 0]]) [hugeBody] 1
      cycleScenario = Scenario recursive (Compound "p" [Var 1, Var 1]) 20 emptyStore [0, 1]
  recursiveCode <- evalMaybe (compileClause recursive)
  let (cycleActual, cycleExpected, cycleAtomic, _) = compareScenario cycleScenario recursiveCode
  cycleActual === Rejected
  cycleActual === cycleExpected
  assert cycleAtomic

prop_clp_propagates_only_after_the_whole_head_matches :: Property
prop_clp_propagates_only_after_the_whole_head_matches = unit $ do
  posted <- evalEither (addRelation RelEq (IntLit 1) (Compound "div" [IntLit 1, Var 0]) emptyStore
    >>= maybe (Right Nothing) (addDomain (Var 0) (Fin 0) (Fin 1)))
  delayed <- evalMaybe posted
  let clause = Clause (Compound "p" [IntLit 0, Atom "expected"])
        [Compound "unreached_body" [StrLit "not interned"]] 0
      makeGoal second = Scenario clause (Compound "p" [Var 0, Atom second]) 20 delayed [0, 1]
  code <- evalMaybe (compileClause clause)
  let (mismatch, mismatchExpected, mismatchAtomic, _) = compareScenario (makeGoal "different") code
      (matched, matchedExpected, matchedAtomic, _) = compareScenario (makeGoal "expected") code
  -- A structural mismatch later in the head masks any delayed error caused
  -- by an earlier temporary binding. Per-instruction CLP posting is unsound.
  mismatch === Rejected
  mismatch === mismatchExpected
  assert mismatchAtomic
  matched === Raised DivisionByZero
  matched === matchedExpected
  assert matchedAtomic
  domainResult <- evalEither (addDomain (Var 0) (Fin 1) (Fin 3) emptyStore)
  domain <- evalMaybe domainResult
  let typedClause = Clause (Compound "p" [Atom "bad", Atom "expected"]) [] 0
      typedGoal second = Scenario typedClause (Compound "p" [Var 0, Atom second]) 20 domain [0]
  typedCode <- evalMaybe (compileClause typedClause)
  let (typeMismatch, typeMismatchExpected, typeMismatchAtomic, _) = compareScenario (typedGoal "different") typedCode
      (typeError, typeErrorExpected, typeErrorAtomic, _) = compareScenario (typedGoal "expected") typedCode
  typeMismatch === Rejected
  typeMismatch === typeMismatchExpected
  assert typeMismatchAtomic
  typeError === Raised (CLPTypeError (Atom "bad"))
  typeError === typeErrorExpected
  assert typeErrorAtomic

prop_nan_signed_zero_and_literal_type_matching :: Property
prop_nan_signed_zero_and_literal_type_matching = unit $ do
  let nan = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      cases =
        [(nan, nan, False), (FloatLit (-0.0), FloatLit 0.0, True),
         (IntLit 1, FloatLit 1.0, False), (Atom "same", Compound "same" [], False)]
  mapM_ (\(headValue, goalValue, matches) -> do
    let clause = Clause (Compound "p" [headValue]) [] 0
        scenario = Scenario clause (Compound "p" [goalValue]) 10 emptyStore [0]
    code <- evalMaybe (compileClause clause)
    let (actual, expected, atomicFailure, counters) = compareScenario scenario code
    actual === expected
    assert atomicFailure
    case (matches, actual, counters) of
      (False, Rejected, Nothing) -> success
      (True, Accepted _ _ _ _ _, Just (_, _, avoided, registers)) -> do
        assert (avoided > 0)
        registers === 0
      _ -> annotateShow actual >> failure) cases

prop_frozen_matched_heads_keep_independent_register_roots :: Property
prop_frozen_matched_heads_keep_independent_register_roots = unit $ do
  let clause = Clause (Compound "p" [Var 0, Var 1])
        [Compound "body_only" [Compound "pair" [Var 0, Var 0], Var 1]] 2
      scenario = Scenario clause (Compound "p" [Var 0, Var 1]) 10 emptyStore [0, 1]
  code <- evalMaybe (compileClause clause)
  let result = runST $ do
        heap <- Heap.newHeap
        (bindings, goal) <- prepare heap scenario
        original <- Heap.freezeHeap heap
        activationResult <- must (Bytecode.activate heap bindings emptyStore goal 10 code)
        activation <- case activationResult of
          Right (Just value) -> pure value
          _ -> error "matching variable head unexpectedly rejected"
        let ready = Bytecode.activationBindings activation
            store = Bytecode.activationStore activation
            body = Bytecode.activationBodyRoots activation
            values branch current = map observe <$> must (Bridge.exportTerms branch current body)
        frozen <- Heap.freezeHeap heap
        before <- values heap ready
        first <- must (NativeCLP.bindInteger heap ready store 0 1)
        firstValues <- case first of
          Right (Just (current, _)) -> values heap current
          _ -> error "first frozen branch binding unexpectedly rejected"
        other <- Heap.thawHeap frozen
        second <- must (NativeCLP.bindInteger other ready store 0 2)
        secondValues <- case second of
          Right (Just (current, _)) -> values other current
          _ -> error "second frozen branch binding unexpectedly rejected"
        repeated <- Heap.thawHeap frozen
        retained <- values repeated ready
        Heap.restoreHeap heap original
        stale <- mapM (Heap.viewRaw heap) body
        reactivatedResult <- must (Bytecode.activate heap bindings emptyStore goal 10 code)
        reactivated <- case reactivatedResult of
          Right (Just value) -> pure value
          _ -> error "replayed activation unexpectedly rejected"
        replayed <- map observe <$> must (Bridge.exportTerms heap
          (Bytecode.activationBindings reactivated) (Bytecode.activationBodyRoots reactivated))
        let stillStale value = case value of Left (Heap.InvalidAddress _) -> True; _ -> False
        pure (before, firstValues, secondValues, retained, replayed,
          all stillStale stale, body /= Bytecode.activationBodyRoots reactivated)
  case result of
    (before, first, second, retained, replayed, stale, freshGeneration) -> do
      before === [observe (Compound "body_only" [Compound "pair" [Var 0, Var 0], Var 1])]
      first === [observe (Compound "body_only" [Compound "pair" [IntLit 1, IntLit 1], Var 1])]
      second === [observe (Compound "body_only" [Compound "pair" [IntLit 2, IntLit 2], Var 1])]
      retained === before
      replayed === before
      assert stale
      assert freshGeneration

prop_stale_head_and_overflow_reject_atomically :: Property
prop_stale_head_and_overflow_reject_atomically = unit $ do
  code <- evalMaybe (compileClause (Clause (Compound "p" [Var 0, Var 1])
    [Compound "body_only" [Var 0, Var 1]] 2))
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0])
        (ready, roots) <- must (Bridge.importTerms heap bindings [Var 0])
        root <- case roots of [one] -> pure one; _ -> error "variable import changed shape"
        mark <- Heap.checkpoint heap
        (_, imported) <- must (Bridge.importTerms heap ready [Compound "p" [Var 0, Var 0]])
        staleGoal <- case imported of [one] -> pure one; _ -> error "goal import changed shape"
        _ <- must (Heap.rollback heap mark)
        before <- heapStats heap
        stale <- Bytecode.activate heap ready emptyStore staleGoal 10 code
        afterStale <- heapStats heap
        overflow <- Bytecode.activate heap ready emptyStore root (maxBound - 1) code
        afterOverflow <- heapStats heap
        values <- must (Bridge.exportTerms heap ready [root])
        let invalid outcome = case outcome of Left (Heap.InvalidAddress _) -> True; _ -> False
            exhausted outcome = case outcome of Left Heap.HeapCapacityExceeded -> True; _ -> False
        pure (invalid stale, exhausted overflow, before, afterStale, afterOverflow, values)
  case result of
    (stale, overflow, before, afterStale, afterOverflow, values) -> do
      assert stale
      assert overflow
      afterStale === before
      afterOverflow === before
      values === [Var 0]

prop_normal_and_measured_activation_match_without_counter_work :: Property
prop_normal_and_measured_activation_match_without_counter_work = unit $ do
  let nan = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      bodyTerm = Compound "body_only" [Compound "pair" [Var 0, Var 0], nan, FloatLit (-0.0)]
      clause = Clause (Compound "p" [Var 0]) [bodyTerm] 1
      scenario = Scenario clause (Compound "p" [Var 0]) 10 emptyStore [0]
      stats activation =
        (Bytecode.activationHeadInstructions activation,
         Bytecode.activationAllocationInstructions activation,
         Bytecode.activationHeadCellsAvoided activation,
         Bytecode.activationRegisterSlots activation)
  code <- evalMaybe (compileClause clause)
  let result = runST $ do
        parent <- Heap.newHeap
        (bindings, goal) <- prepare parent scenario
        initial <- Heap.freezeHeap parent
        normalHeap <- Heap.thawHeap initial
        measuredHeap <- Heap.thawHeap initial
        normalResult <- must (Bytecode.activate normalHeap bindings emptyStore goal 10 code)
        measuredResult <- must (Bytecode.activateMeasured measuredHeap bindings emptyStore goal 10 code)
        (normal, measured) <- case (normalResult, measuredResult) of
          (Right (Just one), Right (Just two)) -> pure (one, two)
          _ -> error "matching normal or measured activation unexpectedly rejected"
        let observeActivation heap activation = accepted heap (Bytecode.activationBindings activation)
              (Bytecode.activationStore activation) goal (Bytecode.activationBodyRoots activation)
            values heap activation = map observe <$> must (Bridge.exportTerms heap
              (Bytecode.activationBindings activation) (Bytecode.activationBodyRoots activation))
            bind heap activation number = do
              bound <- must (NativeCLP.bindInteger heap (Bytecode.activationBindings activation)
                (Bytecode.activationStore activation) 0 number)
              case bound of
                Right (Just (ready, _)) -> map observe <$> must
                  (Bridge.exportTerms heap ready (Bytecode.activationBodyRoots activation))
                _ -> error "binding an independent activation unexpectedly rejected"
        normalBefore <- observeActivation normalHeap normal
        measuredBefore <- observeActivation measuredHeap measured
        frozenNormal <- Heap.freezeHeap normalHeap
        frozenMeasured <- Heap.freezeHeap measuredHeap
        normalBound <- bind normalHeap normal 1
        measuredBound <- bind measuredHeap measured 2
        oldNormal <- Heap.thawHeap frozenNormal
        oldMeasured <- Heap.thawHeap frozenMeasured
        retainedNormal <- values oldNormal normal
        retainedMeasured <- values oldMeasured measured
        normalStillBound <- values normalHeap normal
        pure (normalBefore, measuredBefore, stats normal, stats measured,
          normalBound, measuredBound, retainedNormal, retainedMeasured, normalStillBound)
  case result of
    (normal, measured, normalStats, measuredStats, first, second, retainedNormal, retainedMeasured, firstAgain) -> do
      normal === measured
      normalStats === (0, 0, 0, 0)
      case measuredStats of
        (headInstructions, allocations, avoided, registers) -> do
          assert (headInstructions > 0)
          assert (allocations > 0)
          assert (avoided > 0)
          assert (registers > 0)
      first === [observe (Compound "body_only" [Compound "pair" [IntLit 1, IntLit 1], nan, FloatLit (-0.0)])]
      second === [observe (Compound "body_only" [Compound "pair" [IntLit 2, IntLit 2], nan, FloatLit (-0.0)])]
      retainedNormal === [observe bodyTerm]
      retainedMeasured === retainedNormal
      firstAgain === first

machineHeadGroup :: Group
machineHeadGroup = Group "compiled head matching and registers"
  [("generated head transactions versus legacy import and unification", prop_generated_head_matches_legacy_transaction),
   ("known head shapes avoid construction and register arrays", prop_known_shapes_avoid_head_and_register_allocation),
   ("register pool retains repeated variables and exact scalar bits", prop_register_pool_preserves_repeated_variables_and_scalar_bits),
   ("failed and occurs-check heads never allocate their bodies", prop_failed_head_never_allocates_body_and_is_atomic),
   ("whole structural head precedes one CLP propagation batch", prop_clp_propagates_only_after_the_whole_head_matches),
   ("NaN signed zero and scalar constructor matching", prop_nan_signed_zero_and_literal_type_matching),
   ("frozen matched heads retain independent register roots", prop_frozen_matched_heads_keep_independent_register_roots),
   ("stale head handles and overflow reject atomically", prop_stale_head_and_overflow_reject_atomically),
   ("normal and measured activations preserve independent snapshots", prop_normal_and_measured_activation_match_without_counter_work)]
