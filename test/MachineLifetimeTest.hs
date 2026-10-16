{-# LANGUAGE OverloadedStrings #-}

-- A suspended compiled body is source code plus logical IDs, never a cache
-- of future heap terms. Check that each goal is built in order, that its
-- physical registers preserve the source term, and that GC retains exactly
-- the logical roots needed by the remaining body.
module MachineLifetimeTest (machineLifetimeGroup) where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM, forM_)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word (Word64)
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
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program (Program, addClause)
import Infera.Syntax
import qualified Infera.Unify as Unify

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

must :: Show problem => ST s (Either problem value) -> ST s value
must action = action >>= either (error . show) pure

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText source = annotate source >> evalEither (parseQuery source)

data Observed
  = OAtom String | OVar VarId | OInt Integer | OFloat Word64
  | OChar Char | OString String | OCompound String [Observed]
  deriving (Eq, Show)

observeTerm :: Term -> Observed
observeTerm term = case term of
  Atom value -> OAtom value
  Var value -> OVar value
  IntLit value -> OInt value
  FloatLit value -> OFloat (castDoubleToWord64 value)
  CharLit value -> OChar value
  StrLit value -> OString value
  Compound name arguments -> OCompound name (map observeTerm arguments)

bits :: Term -> Term
bits (FloatLit number) = Compound "$lifetime_float_bits"
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
    combined = Compound "$lifetime_roots" (names ++ terms)

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
            -- Collection may retire unreachable internal substitution keys.
            -- Every other Store field remains exact; the generated small
            -- cases separately compare the complete raw substitution too.
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

-- Decode physical instructions without calling the VM or reconstructing
-- virtual slots. In particular, collect every constructor operand before
-- replacing the destination, which may be one of those just-read registers.
decodeGoal :: VarId -> GoalCode -> Either String (Observed, Bool)
decodeGoal base code = do
  (registers, reused) <- foldM instruction (IM.empty, False) (goalInstructions code)
  result <- operand registers (goalRoot code)
  pure (result, reused)
  where
    valid destination = destination >= 0 && destination < goalRegisterCount code
    operand _ (Local local)
      | local >= 0 = Right (OVar (base + local))
      | otherwise = Left "negative local operand"
    operand registers (Temporary temporary) =
      maybe (Left "read of an uninitialized physical register") Right (IM.lookup temporary registers)
    instruction (registers, reused) operation = case operation of
      GoalOwner destination
        | not (valid destination) -> Left "owner destination outside register array"
        | otherwise -> Right (IM.insert destination (OInt (toInteger base)) registers, reused)
      GoalConstant destination scalar
        | not (valid destination) -> Left "constant destination outside register array"
        | otherwise -> case scalar of
            Var _ -> Left "local emitted as a scalar construction"
            Compound _ _ -> Left "compound emitted as a scalar construction"
            _ -> Right (IM.insert destination (observeTerm scalar) registers, reused)
      GoalCompound destination name children
        | not (valid destination) -> Left "compound destination outside register array"
        | otherwise -> do
            values <- mapM (operand registers) children
            let overwrittenChild = Temporary destination `elem` children
            pure (IM.insert destination (OCompound name values) registers, reused || overwrittenChild)

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["nil", "same", "a", "b", "!", "\955"],
    IntLit <$> Gen.choice [Gen.integral (Range.linear (-3) 3), pure (2 ^ (80 :: Int) + 9)],
    FloatLit <$> Gen.element [-2.5, -0.0, 0.0, 1.5, -1 / 0, 1 / 0,
      castWord64ToDouble 0x7ff8000000000042, castWord64ToDouble 0x7ff8000000000043],
    CharLit <$> Gen.element ['a', '\955', '\0'],
    StrLit <$> Gen.element ["", "kept", "\955", "\0"]
  ]

genTerm :: Int -> Int -> Gen Term
genTerm variables depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency
      [(4, leaf), (3, Compound <$> Gen.element ["box", "pair", "same", "cons"]
        <*> Gen.list (Range.linear 0 3) (genTerm variables (depth - 1)))]
  where
    leaf = Gen.frequency [(3, genScalar), (2, Var <$> Gen.int (Range.linear 0 (variables - 1)))]

data Scenario = Scenario Clause Term VarId Store [(Int, Integer)] Integer
  deriving Show

genScenario :: Gen Scenario
genScenario = do
  count <- Gen.int (Range.linear 1 5)
  body <- Gen.list (Range.linear 0 6)
    (Compound "record" <$> Gen.list (Range.singleton 3) (genTerm count 2))
  final <- Gen.integral (Range.linear (-3) 3)
  let goals = body ++ [Compound "unify" [Var 0, IntLit final]]
  actions <- Gen.list (Range.singleton (length goals))
    ((,) <$> Gen.int (Range.linear 0 (count - 1)) <*> Gen.integral (Range.linear (-3) 3))
  base <- Gen.int (Range.linear 10 100)
  alias <- Gen.int (Range.linear 0 2)
  let substitution = case alias of
        0 -> IM.empty
        1 -> IM.singleton 0 (Var 1)
        _ -> IM.singleton 1 (Var 0)
      initial = emptyStore {stSubst = substitution}
  case addDomains [Var 0] (Fin (-3)) (Fin 3) initial of
    Right (Just store) -> pure (Scenario
      (Clause (Compound "root" [Var 0]) goals count)
      (Compound "root" [Var 0]) base store actions final)
    _ -> error "generated initial domain unexpectedly rejected"

prepare :: Heap.Heap s -> Scenario -> ST s (Bridge.Bindings, Heap.Address)
prepare heap (Scenario _ goal _ store _ _) = do
  bindings <- must (Bridge.newBindings heap [0, 1, 2])
  ready <- must (Bridge.syncState heap bindings ((Reference.initialState 3) {Reference.ssStore = store}))
  (imported, roots) <- must (Bridge.importTerms heap ready [goal])
  case roots of
    [root] -> pure (imported, root)
    _ -> error "goal import changed root count"

data WriteResult = WriteAccepted | WriteRejected | WriteError SolveError
  deriving (Eq, Show)

writeLocal :: Heap.Heap s -> Bridge.Bindings -> Store -> VarId -> (Int, Integer)
  -> ST s (Bridge.Bindings, Store, WriteResult)
writeLocal heap bindings store base (local, value) = do
  (ready, roots) <- must (Bridge.importTerms heap bindings [Var (base + local), IntLit value])
  case roots of
    [left, right] -> do
      result <- must (NativeCLP.unify heap ready store left right)
      case result of
        Left problem -> pure (ready, store, WriteError (errorTerms bits problem))
        Right Nothing -> pure (ready, store, WriteRejected)
        Right (Just (updated, nextStore)) -> pure (updated, nextStore, WriteAccepted)
    _ -> error "write import changed root count"

data BodyObservation = BodyObservation WriteResult Store [Observed] [Observed] [VarId]
  deriving (Eq, Show)

bodyObservation :: Heap.Heap s -> Bridge.Bindings -> Store -> Heap.Address -> WriteResult
  -> ST s BodyObservation
bodyObservation heap bindings store root write = do
  raw <- must (Bridge.exportRawTerms heap bindings [root])
  values <- must (Bridge.exportTerms heap bindings [root])
  pure (BodyObservation write (storeBits store) (map observeTerm raw)
    (map observeTerm values) (Bridge.bindingVariables bindings))

-- The oracle imports the complete renamed source clause before its single
-- head/CLP transaction, exactly as the previous implementation did. The new
-- branch is checked after every individual body construction and local write.
legacySequence :: Heap.Heap s -> Bridge.Bindings -> Heap.Address -> Scenario
  -> ST s [BodyObservation]
legacySequence heap bindings goal (Scenario clause _ base store actions _) = do
  let count = max 1 (clauseNVars clause)
  (ready, roots) <- must (Bridge.importTerms heap bindings
    (map Var [base .. base + count - 1] ++
      Unify.renameTerm base (clauseHead clause) : map (Unify.renameBody base) (clauseBody clause)))
  case drop count roots of
    headRoot : bodyRoots -> do
      result <- must (NativeCLP.unify heap ready store goal headRoot)
      case result of
        Right (Just (matched, acceptedStore)) -> go matched acceptedStore bodyRoots actions
        _ -> error "generated legacy head unexpectedly rejected"
    _ -> error "legacy import changed root count"
  where
    go _ _ [] [] = pure []
    go ready current (root : roots) (action : remaining) = do
      (updated, nextStore, write) <- writeLocal heap ready current base action
      observed <- bodyObservation heap updated nextStore root write
      rest <- go updated nextStore roots remaining
      pure (observed : rest)
    go _ _ _ _ = error "generated legacy body/action lengths differ"

incrementalSequence :: Bool -> Heap.Heap s -> Bridge.Bindings -> Heap.Address
  -> Scenario -> ClauseCode -> ST s ([BodyObservation], [(Int, Int)], (Int, Int, Int, Int))
incrementalSequence measured heap bindings goal (Scenario _ _ base store actions _) code = do
  let activate = if measured then Bytecode.activateHeadMeasured else Bytecode.activateHead
      materialize = if measured then Bytecode.materializeNextMeasured else Bytecode.materializeNext
  result <- must (activate heap bindings store goal base code)
  case result of
    Right (Just headResult) -> do
      (observations, counters) <- go materialize (Bytecode.headBindings headResult)
        (Bytecode.headStore headResult) (Bytecode.headBodyFrame headResult) actions
      pure (observations, counters, (Bytecode.headInstructions headResult,
        Bytecode.headAllocationInstructions headResult, Bytecode.headCellsAvoided headResult,
        Bytecode.headRegisterSlots headResult))
    _ -> error "generated compiled head unexpectedly rejected"
  where
    go _ _ _ Nothing [] = pure ([], [])
    go materialize ready current (Just frame) (action : remaining) = do
      next <- must (materialize heap ready frame)
      case next of
        Just step -> do
          (updated, nextStore, write) <- writeLocal heap ready current base action
          observed <- bodyObservation heap updated nextStore (Bytecode.stepRoot step) write
          (rest, counters) <- go materialize updated nextStore (Bytecode.stepNextFrame step) remaining
          pure (observed : rest,
            (Bytecode.stepAllocationInstructions step, Bytecode.stepRegisterSlots step) : counters)
        Nothing -> error "nonempty frame did not materialize a goal"
    go _ _ _ _ _ = error "generated compiled body/action lengths differ"

compareScenario :: Scenario -> ClauseCode
  -> ([BodyObservation], [BodyObservation], [BodyObservation], [BodyObservation],
      [(Int, Int)], [(Int, Int)], (Int, Int, Int, Int), (Int, Int, Int, Int), Bool)
compareScenario scenario code = runST $ do
  original <- Heap.newHeap
  (bindings, goal) <- prepare original scenario
  frozen <- Heap.freezeHeap original
  originalValue <- must (Bridge.exportTerms original bindings [goal])
  native <- Heap.thawHeap frozen
  (actual, normalCounters, normalHead) <- incrementalSequence False native bindings goal scenario code
  measured <- Heap.thawHeap frozen
  (counted, measuredCounters, measuredHead) <- incrementalSequence True measured bindings goal scenario code
  repeated <- Heap.thawHeap frozen
  (replay, _, _) <- incrementalSequence False repeated bindings goal scenario code
  old <- Heap.thawHeap frozen
  expected <- legacySequence old bindings goal scenario
  retained <- must (Bridge.exportTerms original bindings [goal])
  pure (actual, counted, replay, expected, normalCounters, measuredCounters,
    normalHead, measuredHead, map observeTerm retained == map observeTerm originalValue)

prop_generated_sequential_body_and_physical_register_parity :: Property
prop_generated_sequential_body_and_physical_register_parity = withTests 500 . property $ do
  scenario@(Scenario clause goal base store _ final) <- forAll genScenario
  code <- evalMaybe (compileClause clause)
  length (codeGoals code) === length (clauseBody clause)
  decoded <- forM (zip (codeGoals code) (clauseBody clause)) $ \(compiled, template) -> do
    (value, reused) <- evalEither (decodeGoal base compiled)
    value === observeTerm (Unify.renameBody base template)
    bodyKey (goalCall compiled) === maybe (error "generated goal has no key") id (functorOf template)
    observeTerm (bodyTemplate (goalCall compiled)) === observeTerm template
    goalVariables compiled === IS.fromList (termVarIds template)
    pure reused
  forM_ (zip [0 :: Int ..] (codeGoals code)) $ \(index, compiled) ->
    goalSuffixVariables compiled === IS.fromList (concatMap termVarIds (drop index (clauseBody clause)))
  classify "physical destination reuses a child" (or decoded)
  let (actual, measured, replay, expected, normalCounts, measuredCounts, normalHead, measuredHead, intact) =
        compareScenario scenario code
  actual === expected
  measured === expected
  replay === expected
  normalCounts === replicate (length (clauseBody clause)) (0, 0)
  normalHead === (0, 0, 0, 0)
  measuredCounts === [(length (goalInstructions compiled), goalRegisterCount compiled) | compiled <- codeGoals code]
  case measuredHead of
    (matched, _, avoided, _) -> assert (matched > 0 && avoided > 0)
  assert intact
  -- The same generated source clause also executes in all three engines.
  -- These deliberately small runs avoid collection, permitting comparison
  -- of every raw internal substitution entry as well as public answers.
  baseProgram <- load "<- notable.\nrecord _ _ _."
  let program = addClause clause baseProgram
      query = Query [goal] [("A", 0), ("B", 1), ("Unused", 2)] 3
      state = (Reference.initialState base) {Reference.ssStore = store}
      environment = Reference.mkEnv program
      reference = Reference.solveGoals environment 100 state [goal]
  compiled <- evalEither (Machine.startGoalsWithBackend Machine.Bytecode environment 100 state [goal])
  interpreted <- evalEither (Machine.startGoalsWithBackend Machine.Interpreted environment 100 state [goal])
  (found, _) <- evalEither (drain compiled)
  (oldFound, _) <- evalEither (drain interpreted)
  events query found === events query reference
  events query oldFound === events query reference
  [storeBits (Reference.ssStore accepted) | Reference.Found accepted <- found] ===
    [storeBits (Reference.ssStore accepted) | Reference.Found accepted <- reference]
  [storeBits (Reference.ssStore accepted) | Reference.Found accepted <- oldFound] ===
    [storeBits (Reference.ssStore accepted) | Reference.Found accepted <- reference]
  case [Reference.projectAnswer query accepted | Reference.Found accepted <- found] of
    [answer] -> lookup "A" (Reference.answerBindings answer) === Just (IntLit final)
    other -> annotateShow other >> failure

prop_physical_reuse_preserves_repeated_scalars_and_source_ids :: Property
prop_physical_reuse_preserves_repeated_scalars_and_source_ids = unit $ do
  let nan1 = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      nan2 = FloatLit (castWord64ToDouble 0x7ff8000000000043)
      nested = Compound "record" [
        Compound "pair" [Compound "box" [Var 0], Compound "pair" [Var 1, Var 0]],
        Compound "typed" [IntLit 1, FloatLit 1, FloatLit (-0.0), FloatLit 0.0,
          nan1, nan1, nan2, Atom "same", Compound "same" [], CharLit 'a', StrLit "a"],
        Compound "tail" [Compound "box" [IntLit 7], Compound "box" [IntLit 7]]]
      clause = Clause (Compound "root" [Var 0]) [nested] 2
      scenario = Scenario clause (Compound "root" [Var 0]) 20 emptyStore [(1, 9)] 0
  code <- evalMaybe (compileClause clause)
  compiled <- case codeGoals code of [one] -> pure one; _ -> failure
  (decoded, reused) <- evalEither (decodeGoal 20 compiled)
  decoded === observeTerm (Unify.renameBody 20 nested)
  assert reused
  assert (goalRegisterCount compiled < length (goalInstructions compiled))
  let (actual, measured, replay, expected, _, counters, _, _, intact) = compareScenario scenario code
  actual === expected
  measured === expected
  replay === expected
  counters === [(length (goalInstructions compiled), goalRegisterCount compiled)]
  assert intact

heapStats :: Heap.Heap s -> ST s (Int, Int, (Int, Int))
heapStats heap = (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap

prop_lookup_variables_is_read_only_ordered_and_strict :: Property
prop_lookup_variables_is_read_only_ordered_and_strict = unit $ do
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0, 2, 7])
        let state = (Reference.initialState 8)
              {Reference.ssStore = emptyStore {stSubst = IM.fromList [(0, Var 2), (7, IntLit 9)]}}
        ready <- must (Bridge.syncState heap bindings state)
        before <- heapStats heap
        roots <- must (Bridge.lookupVariables heap ready [7, 0, 2, 0, 7])
        raw <- must (Bridge.exportRawTerms heap ready roots)
        values <- must (Bridge.exportTerms heap ready roots)
        missing <- Bridge.lookupVariables heap ready [2, 99, 0]
        empty <- must (Bridge.lookupVariables heap ready [])
        after <- heapStats heap
        prefix <- Heap.freezeHeap heap
        (extended, _) <- must (Bridge.importTerms heap ready [Var 100])
        Heap.restoreHeap heap prefix
        staleEmpty <- Bridge.lookupVariables heap extended []
        stalePresent <- Bridge.lookupVariables heap extended [0]
        restoredStats <- heapStats heap
        pure (map observeTerm raw, map observeTerm values, length roots, missing, empty,
          staleEmpty, stalePresent, before == after && after == restoredStats)
  case result of
    (raw, values, count, missing, empty, staleEmpty, stalePresent, unchanged) -> do
      raw === map observeTerm [Var 7, Var 0, Var 2, Var 0, Var 7]
      values === map observeTerm [IntLit 9, Var 2, Var 2, Var 2, IntLit 9]
      count === 5
      missing === Left Heap.IncompatibleBindings
      empty === []
      assert (case staleEmpty of Left (Heap.InvalidAddress _) -> True; _ -> False)
      assert (case stalePresent of Left (Heap.InvalidAddress _) -> True; _ -> False)
      assert unchanged

prop_future_locals_survive_collection_without_resurrecting_dead_roots :: Property
prop_future_locals_survive_collection_without_resurrecting_dead_roots = unit $ do
  let clause = Clause (Compound "root" [])
        [Compound "first" [Var 0], Compound "second" [Var 1], Compound "third" [Var 2, Var 1]] 3
  code <- evalMaybe (compileClause clause)
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0])
        (ready, roots) <- must (Bridge.importTerms heap bindings [Compound "root" []])
        goal <- case roots of [one] -> pure one; _ -> error "root import count"
        activation <- must (Bytecode.activateHeadMeasured heap ready emptyStore goal 20 code)
        headResult <- case activation of Right (Just one) -> pure one; _ -> error "fact head rejected"
        frame <- maybe (error "missing first frame") pure (Bytecode.headBodyFrame headResult)
        headSize <- Heap.heapSize heap
        first <- must (Bytecode.materializeNextMeasured heap (Bytecode.headBindings headResult) frame)
        firstStep <- maybe (error "missing first step") pure first
        remaining <- maybe (error "missing later frame") pure (Bytecode.stepNextFrame firstStep)
        let acceptedState = (Reference.initialState 23) {Reference.ssStore = Bytecode.headStore headResult}
            protected = 0 : Bytecode.frameVariables remaining
        frozen <- Heap.freezeHeap heap
        (collected, live, state, relocated) <- must
          (Bridge.rebuild heap (Bytecode.headBindings headResult) protected acceptedState [])
        before <- heapStats collected
        current <- must (Bridge.lookupVariables collected live [22, 21, 21])
        missing <- Bridge.lookupVariables collected live [20]
        after <- heapStats collected
        second <- must (Bytecode.materializeNextMeasured collected live remaining)
        secondStep <- maybe (error "missing second step") pure second
        secondRaw <- must (Bridge.exportRawTerms collected live [Bytecode.stepRoot secondStep])
        finalFrame <- maybe (error "missing final frame") pure (Bytecode.stepNextFrame secondStep)
        (lastHeap, lastBindings, lastState, _) <- must
          (Bridge.rebuild collected live (0 : Bytecode.frameVariables finalFrame) state [])
        final <- must (Bytecode.materializeNext lastHeap lastBindings finalFrame)
        finalStep <- maybe (error "missing final step") pure final
        finalRaw <- must (Bridge.exportRawTerms lastHeap lastBindings [Bytecode.stepRoot finalStep])
        retained <- Heap.thawHeap frozen
        retainedRaw <- must (Bridge.exportRawTerms retained (Bytecode.headBindings headResult)
          [Bytecode.stepRoot firstStep])
        pure (headSize, Bytecode.headRegisterSlots headResult, Bytecode.headAllocationInstructions headResult,
          Bytecode.frameVariables frame, Bytecode.frameVariables remaining,
          Bridge.bindingVariables live, map observeTerm secondRaw, map observeTerm finalRaw,
          map observeTerm retainedRaw, length current, missing, relocated,
          before == after, Bridge.bindingVariables lastBindings, storeBits (Reference.ssStore lastState),
          case Bytecode.stepNextFrame finalStep of Nothing -> True; Just _ -> False)
  case result of
    (headSize, registers, allocations, firstVars, suffixVars, liveVars, second, final, retained,
      currentCount, missing, relocated, unchanged, lastVars, finalStore, emptyFrame) -> do
      assert (headSize < 20)
      registers === 0
      allocations === 0
      firstVars === [20, 21, 22]
      suffixVars === [21, 22]
      liveVars === [0, 21, 22]
      second === [observeTerm (Compound "second" [Var 21])]
      final === [observeTerm (Compound "third" [Var 22, Var 21])]
      retained === [observeTerm (Compound "first" [Var 20])]
      currentCount === 3
      missing === Left Heap.IncompatibleBindings
      relocated === []
      assert unchanged
      lastVars === [0, 21, 22]
      finalStore === emptyStore
      assert emptyFrame

unreachableBody :: String
unreachableBody = concat [", sink (future_" ++ show index ++ " (payload " ++ show index ++ ") X)"
  | index <- [0 :: Int .. 2999]]

assertSmallEarlyBody :: Int -> Machine.Metrics -> PropertyT IO ()
assertSmallEarlyBody reached metrics = do
  annotateShow metrics
  assert (Machine.metricCompiledActivations metrics > 0)
  assert (Machine.metricHeadInstructions metrics > 0)
  Machine.metricBodyGoalsMaterialized metrics === reached
  assert (Machine.metricBodyAllocationInstructions metrics <= 3)
  assert (Machine.metricMaxActivationRegisters metrics <= 3)
  assert (Machine.metricMaxHeapCells metrics <= 96)
  assert (Machine.metricMaxTasks metrics <= 12)

prop_early_failure_and_error_do_not_allocate_future_body :: Property
prop_early_failure_and_error_do_not_allocate_future_body = unit $ do
  forM_ [("fail", Nothing), ("missing", Just (UnknownPredicate ("missing", 0)))] $ \(first, problem) -> do
    program <- load ("<- notable.\nwide : nondet (any: <=>).\nwide X <- " ++ first ++ unreachableBody ++ ".\nsink _.\n")
    query <- queryText "(wide _ ; Result = done)?"
    initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
    (actual, metrics) <- evalEither (drain initial)
    events query actual === events query (Reference.solveQuery program query)
    events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
    [failure' | Reference.BranchError failure' <- actual] === maybe [] (: []) problem
    case [Reference.projectAnswer query state | Reference.Found state <- actual] of
      [answer] -> Reference.answerBindings answer === [("Result", Atom "done")]
      other -> annotateShow other >> failure
    assertSmallEarlyBody 1 metrics

prop_foreign_cut_does_not_allocate_remaining_compiled_body :: Property
prop_foreign_cut_does_not_allocate_remaining_compiled_body = unit $ do
  base <- load ("<- notable.\nwide : nondet unsafe (any: <=>).\nabort : nondet unsafe.\nwide X <- abort" ++ unreachableBody ++ ".\nsink _.\n")
  let foreignClause = Clause (Atom "abort") [Compound "$cut" [IntLit (-7)], Atom "fail"] 0
      program = addClause foreignClause base
  query <- queryText "(wide _ ; Result = done)?"
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, metrics) <- evalEither (drain initial)
  events query actual === events query (Reference.solveQuery program query)
  events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
  [owner | Reference.CutMarker owner <- actual] === [-7]
  [() | Reference.Found _ <- actual] === []
  -- The abort helper's fail is now compiled too; its cut allocates no graph.
  Machine.metricCompiledCuts metrics === 1
  assertSmallEarlyBody 2 metrics

prop_future_and_earlier_live_values_survive_tail_collection :: Property
prop_future_and_earlier_live_values_survive_tail_collection = unit $ do
  program <- load $ unlines
    [ "<- notable.", "hold (pair retained retained).", "make (box fresh).",
      "combine Left Right (pair Left Right).",
      "root Result <- hold Shared, down 10000 _, make Future, combine Shared Future Result.",
      "down 0 done.", "down N Result <- N > 0, M is N - 1, down M Result."
    ]
  query <- queryText "root Result?"
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, metrics) <- evalEither (drain initial)
  events query actual === events query (Reference.solveQuery program query)
  events query actual === events query (Machine.solveQueryWithBackend Machine.Interpreted program query)
  case [Reference.projectAnswer query state | Reference.Found state <- actual] of
    [answer] -> Reference.answerBindings answer === [("Result", Compound "pair"
      [Compound "pair" [Atom "retained", Atom "retained"], Compound "box" [Atom "fresh"]])]
    other -> annotateShow other >> failure
  annotateShow metrics
  assert (Machine.metricBodyGoalsMaterialized metrics > 20000)
  assert (Machine.metricBodyAllocationInstructions metrics > 20000)
  assert (Machine.metricCollections metrics > 0)
  assert (Machine.metricTailCalls metrics >= 9000)
  assert (Machine.metricMaxTasks metrics <= 16)
  assert (Machine.metricMaxHeapCells metrics <= 4096)

drainTraced :: Machine.Checkpoint -> Either Heap.HeapError ([Trace.TraceEvent], Reference.Search)
drainTraced checkpoint = do
  (trace, step) <- Machine.resumeTraced checkpoint
  case step of
    Machine.Finished -> pure (trace, [])
    Machine.Yield item next -> do
      (laterTrace, later) <- drainTraced next
      pure (trace ++ laterTrace, item : later)

prop_interleaved_retries_scopes_contracts_fuel_and_source_traces :: Property
prop_interleaved_retries_scopes_contracts_fuel_and_source_traces = unit $ do
  program <- load $ unlines
    [ "<- notable.", "pick a.", "pick b.", "pair X (pair X X).",
      "root Result <- pick X, pair X Mid, pair Mid Result.",
      "broken X <- X is 1 / 0, missing.",
      "out : nondet (int: =>).", "out X <- free X, late.", "out 2.",
      "free _.", "late.", "wrapped X <- out X.",
      "limited : nondet unsafe (any: <=>).", "limited X <- pick X, !, pair X _.",
      "memo : dynamic.", "saved : unsafe (any: <=>).", "saved X <- assert (memo X), memo X."
    ]
  forM_
    [ "root Result?", "(broken X ; root Result)?", "wrapped X?", "once (root Result)?",
      "findall Result (root Result) List?", "not (root absent)?",
      "(root Result -> pair Result Again ; Again = empty)?", "limited X?",
      "(saved discarded, fail ; saved retained)?"
    ] $ \source -> do
      query <- queryText source
      _ <- compareQuery program query
      compiled <- evalEither (Machine.startTracedWithBackend Machine.Bytecode program query)
      interpreted <- evalEither (Machine.startTracedWithBackend Machine.Interpreted program query)
      (trace, actual) <- evalEither (drainTraced compiled)
      (oldTrace, expected) <- evalEither (drainTraced interpreted)
      trace === oldTrace
      assert (not (null trace))
      events query actual === events query expected
      (replayedTrace, replayed) <- evalEither (drainTraced compiled)
      replayedTrace === trace
      events query replayed === events query actual
      forM_ [0, 1, 2, 3, 5] $ \fuel -> do
        let environment = Reference.mkEnv program
            state = Reference.initialState (queryNVars query)
            expectedFuel = Reference.solveGoals environment fuel state (queryGoals query)
        forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
          initial <- evalEither (Machine.startGoalsWithBackend backend environment fuel state (queryGoals query))
          (found, _) <- evalEither (drain initial)
          events query found === events query expectedFuel
  query <- queryText "root Result?"
  compiled <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  interpreted <- evalEither (Machine.startWithBackend Machine.Interpreted program query)
  first <- evalEither (Machine.resume compiled)
  oldFirst <- evalEither (Machine.resume interpreted)
  case (first, oldFirst) of
    (Machine.Yield retained next, Machine.Yield oldRetained oldNext) -> do
      let prefix = events query [retained]
      _ <- evalIO (evaluate (length (show prefix)))
      (oldRest, _) <- evalEither (drain oldNext)
      (rest, _) <- evalEither (drain next)
      (repeated, _) <- evalEither (drain next)
      (allAgain, _) <- evalEither (drain compiled)
      events query rest === events query oldRest
      events query rest === events query repeated
      prefix === events query [retained]
      prefix === events query [oldRetained]
      prefix ++ events query rest === events query allAgain
    _ -> failure

machineLifetimeGroup :: Group
machineLifetimeGroup = Group "compiled body register lifetimes"
  [ ("generated sequential bodies raw stores frozen branches and physical registers", prop_generated_sequential_body_and_physical_register_parity),
    ("physical reuse preserves scalar bits and repeated source locals", prop_physical_reuse_preserves_repeated_scalars_and_source_ids),
    ("logical-root lookup is ordered read-only and rejects stale bindings", prop_lookup_variables_is_read_only_ordered_and_strict),
    ("future locals survive collection without dead-root resurrection", prop_future_locals_survive_collection_without_resurrecting_dead_roots),
    ("early failure and error do not allocate future body goals", prop_early_failure_and_error_do_not_allocate_future_body),
    ("foreign cut does not allocate remaining compiled body", prop_foreign_cut_does_not_allocate_remaining_compiled_body),
    ("future and earlier live values survive tail collection", prop_future_and_earlier_live_values_survive_tail_collection),
    ("interleaved retries scopes contracts fuel and source traces", prop_interleaved_retries_scopes_contracts_fuel_and_source_traces)
  ]
