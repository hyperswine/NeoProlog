{-# LANGUAGE OverloadedStrings #-}

-- Source-owned lazy caches must remain correct after public record edits and
-- across immutable program versions. Compare both cached and deliberately
-- uncached bytecode execution with the independent interpreted paths.
module MachineCacheTest (machineCacheGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP
import Infera.Compile hiding (Cut)
import qualified Infera.Compile.Cache as Cache
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import Infera.Infer (inferProgram)
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program
import Infera.Syntax
import qualified Infera.Unify as Unify

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText source = annotate source >> evalEither (parseQuery source)

bits :: Term -> Term
bits (FloatLit number) = Compound "$cache_float_bits"
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
    combined = Compound "$cache_roots" (names ++ terms)

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

rawStores :: Reference.Search -> [Store]
rawStores items = [storeBits (Reference.ssStore state) | Reference.Found state <- items]

withoutCaches :: Program -> Program
withoutCaches program = program {progPreds = Map.map
  (\definition -> definition {predClauseCache = Cache.emptyClauseCache}) (progPreds program)}

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
      uncached = Machine.solveQueryWithBackend Machine.Bytecode (withoutCaches program) query
      interpreted = Machine.solveQueryWithBackend Machine.Interpreted program query
      reference = Reference.solveQuery program query
  events query actual === events query uncached
  events query actual === events query interpreted
  events query actual === events query reference
  rawStores actual === rawStores uncached
  pure actual

values :: String -> Query -> Reference.Search -> [Term]
values name query items = [value | Reference.Found state <- items,
  Just value <- [lookup name (Reference.answerBindings (Reference.projectAnswer query state))]]

unify :: Term -> Term -> Term
unify left right = Compound "unify" [left, right]

editPred :: PredKey -> (Pred -> Pred) -> Program -> Program
editPred key update program = program {progPreds = Map.adjust update key (progPreds program)}

data InstructionView
  = VariableInstruction Slot Int | ConstantInstruction Slot Term | OwnerInstruction Slot
  | CompoundInstruction Slot String [Slot]
  deriving (Eq, Show)

data HeadView
  = VariableHead Int | ConstantHead Slot Term | CompoundHead Slot String Int Int
  deriving (Eq, Show)

data CodeView = CodeView Int Int Int [InstructionView] [HeadView] [(Slot, PredKey, Term)] [Term]
  deriving (Eq, Show)

codeView :: Maybe ClauseCode -> Maybe CodeView
codeView = fmap (\code -> CodeView (codeVariableCount code) (codeSlotCount code)
  (codeUnsharedSlotCount code) (map instruction (codeInstructions code))
  (map headInstruction (codeHeadInstructions code))
  [(bodySlot call, bodyKey call, bits (bodyTemplate call)) | call <- codeBody code]
  (map (bits . controlTemplate) (codeControls code)))
  where
    instruction (UseVariable slot variable) = VariableInstruction slot variable
    instruction (PutConstant slot value) = ConstantInstruction slot (bits value)
    instruction (PutOwner slot) = OwnerInstruction slot
    instruction (PutCompound slot name children) = CompoundInstruction slot name children
    headInstruction (HeadVariable variable) = VariableHead variable
    headInstruction (HeadConstant slot value) = ConstantHead slot (bits value)
    headInstruction (HeadCompound slot name arity width) = CompoundHead slot name arity width

assertLookup :: Bool -> Int -> Clause -> Cache.ClauseCache -> PropertyT IO ()
assertLookup expectedHit ordinal source cache = do
  let (hit, compiled) = Cache.lookupClauseCode ordinal source cache
  hit === expectedHit
  codeView compiled === codeView (compileClause source)

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["a", "same", "\955"],
    IntLit <$> Gen.integral (Range.linear (-3) 3),
    FloatLit <$> Gen.element [-0.0, 0.0, 1.5, castWord64ToDouble 0x7ff8000000000042],
    CharLit <$> Gen.element ['a', '\955'], StrLit <$> Gen.element ["", "same", "\955"]
  ]

genTerm :: Int -> Int -> Gen Term
genTerm variables depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency [(4, leaf), (3, Compound <$> Gen.element ["box", "pair", "same"]
      <*> Gen.list (Range.linear 0 3) (genTerm variables (depth - 1)))]
  where
    leaf | variables <= 0 = genScalar
         | otherwise = Gen.frequency [(3, genScalar), (2, Var <$> Gen.int (Range.linear 0 (variables - 1)))]

genClause :: Gen Clause
genClause = do
  variables <- Gen.int (Range.linear 0 4)
  arguments <- Gen.list (Range.singleton 2) (genTerm variables 2)
  body <- Gen.list (Range.linear 0 3)
    (Compound "body" <$> Gen.list (Range.linear 0 3) (genTerm variables 2))
  pure (Clause (Compound "p" arguments) body variables)

prop_generated_exact_witnesses_and_immutable_cache_versions :: Property
prop_generated_exact_witnesses_and_immutable_cache_versions = withTests 300 . property $ do
  source <- forAll genClause
  ordinal <- forAll (Gen.int (Range.linear 0 6))
  change <- forAll (Gen.int (Range.linear 0 3))
  let unsupported = Clause (IntLit 42) [] 0
      entries = IM.fromList [(ordinal, source), (ordinal + 1, unsupported)]
      old = Cache.buildClauseCache entries
      changed = case change of
        0 -> source {clauseBody = clauseBody source ++ [Atom "true"]}
        1 -> source {clauseNVars = clauseNVars source + 1}
        2 -> source {clauseHead = Compound "changed" [clauseHead source]}
        _ -> source {clauseNVars = -1}
      updated = Cache.insertClause ordinal changed old
      inserted = foldr (uncurry Cache.insertClause) Cache.emptyClauseCache (IM.toList entries)
  assertLookup True ordinal source old
  assertLookup True ordinal source inserted
  assertLookup False ordinal changed old
  assertLookup True ordinal changed updated
  assertLookup False ordinal source updated
  assertLookup True ordinal source old
  assertLookup True (ordinal + 1) unsupported old
  assertLookup True (ordinal + 1) unsupported updated
  assertLookup False (ordinal + 10) changed old

prop_generated_direct_record_edits_and_retained_programs :: Property
prop_generated_direct_record_edits_and_retained_programs = withTests 300 . property $ do
  numbers <- forAll (Gen.list (Range.linear 0 8) (Gen.integral (Range.linear (-3) 3)))
  replacement <- forAll (Gen.integral (Range.linear (-3) 3))
  appended <- forAll (Gen.integral (Range.linear (-3) 3))
  base <- load "<- notable.\np : nondet (any: <=>).\np _ <- fail.\nroot : nondet (any: <=>).\nroot X <- p X."
  let fact value = Clause (Compound "p" [Var 0]) [unify (Var 0) (IntLit value)] 1
      old = foldl (flip addClause) base (map fact numbers)
      -- Deliberately leave predClauseCache untouched. The changed local
      -- count also makes a stale plan's fresh-ID convention observable.
      changedClause = (fact replacement) {clauseNVars = 2}
      changed = editPred ("p", 1)
        (\definition -> definition {predClauses = IM.insert 0 changedClause (predClauses definition)}) old
      extended = addClause (fact appended) changed
  query <- queryText "root X?"
  retained <- evalEither (Machine.startWithBackend Machine.Bytecode old query)
  (before, _) <- evalEither (drain retained)
  _ <- evalIO (evaluate (length (show (events query before))))
  values "X" query before === map IntLit numbers
  current <- compareQuery changed query
  values "X" query current === map IntLit (replacement : numbers)
  later <- compareQuery extended query
  values "X" query later === map IntLit (replacement : numbers ++ [appended])
  forM_ [(old, before), (changed, current), (extended, later)] $ \(program, actual) -> do
    let reference = Reference.solveQuery program query
        interpreted = Machine.solveQueryWithBackend Machine.Interpreted program query
    rawStores actual === rawStores reference
    rawStores actual === rawStores interpreted
  (again, _) <- evalEither (drain retained)
  events query again === events query before
  rawStores again === rawStores before
  oldAgain <- compareQuery old query
  events query oldAgain === events query before

prop_exact_float_constructor_and_fallback_witnesses :: Property
prop_exact_float_constructor_and_fallback_witnesses = unit $ do
  let nan1 = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      nan2 = FloatLit (castWord64ToDouble 0x7ff8000000000043)
      clause scalar = Clause (Compound "p" [Var 0]) [unify (Var 0) scalar] 1
      originals = [FloatLit 0.0, FloatLit (-0.0), nan1, nan2,
        IntLit 1, FloatLit 1, Atom "same", Compound "same" [], CharLit 'a', StrLit "a"]
      unsupported = Clause (Compound "p" [Var 0]) [unify (Var 0) (Atom "fallback")] (-1)
  forM_ originals $ \scalar -> do
    let source = clause scalar
        cache = Cache.insertClause 3 source Cache.emptyClauseCache
    assertLookup True 3 source cache
    forM_ originals $ \replacement ->
      assertLookup (bits scalar == bits replacement) 3 (clause replacement) cache
    assertLookup False 3 unsupported cache
  let fallbackCache = Cache.insertClause 3 unsupported Cache.emptyClauseCache
  assertLookup True 3 unsupported fallbackCache
  codeView (snd (Cache.lookupClauseCode 3 unsupported fallbackCache)) === Nothing
  assertLookup False 3 (clause nan1) fallbackCache
  let updated = Cache.insertClause 3 (clause nan1) fallbackCache
  assertLookup True 3 (clause nan1) updated
  assertLookup True 3 unsupported fallbackCache
  -- Neither showing nor inserting an untouched cache may compile its source.
  let unreachable = Clause (Compound "unreached" []) (error "unreached cache plan was forced") 0
      lazyCache = Cache.insertClause 7 unreachable Cache.emptyClauseCache
  shown <- evalIO (evaluate (length (show lazyCache)))
  assert (shown > 0)
  base <- load "<- notable.\np : nondet (any: <=>)."
  query <- queryText "p X?"
  forM_ originals $ \scalar -> do
    let old = addClause (clause scalar) base
    retained <- evalEither (Machine.startWithBackend Machine.Bytecode old query)
    (before, _) <- evalEither (drain retained)
    map bits (values "X" query before) === [bits scalar]
    forM_ originals $ \replacement -> do
      let changed = editPred ("p", 1) (\definition -> definition
            {predClauses = IM.singleton 0 (clause replacement)}) old
      actual <- compareQuery changed query
      map bits (values "X" query actual) === [bits replacement]
      rawStores actual === rawStores (Reference.solveQuery changed query)
    (again, _) <- evalEither (drain retained)
    events query again === events query before

prop_selected_only_lazy_plans_and_scope_memoization :: Property
prop_selected_only_lazy_plans_and_scope_memoization = unit $ do
  base <- load $ unlines
    [ "<- notable.", "p : nondet (any: <=>).", "p 1.", "p 2.",
      "root : nondet unsafe (any: <=>).",
      "root List <- once (p _), findall X (p X) List, not (p absent), (p _ ; true).",
      "unreached : unsafe.", "large_unused : unsafe."
    ]
  let poison = Clause (Atom "unreached") (error "an unselected predicate was compiled") 0
      large = Clause (Atom "large_unused")
        [Compound "data" [Compound ("unused_" ++ show index) [IntLit (fromIntegral index)]]
          | index <- [0 :: Int .. 2999]] (-1)
      program = addClause large (addClause poison base)
  query <- queryText "root List?"
  initial <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode program query)
  (actual, metrics) <- evalEither (drain initial)
  values "List" query actual === replicate 3 (mkList [IntLit 1, IntLit 2] Nothing)
  events query actual === events query (Reference.solveQuery program query)
  Machine.metricPredicateCacheHits metrics === 3
  Machine.metricPredicateCacheMisses metrics === 0
  Machine.metricCodeCacheHits metrics === 3
  assert (Machine.metricCompiledActivations metrics > 0)
  normal <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  (plain, disabled) <- evalEither (drain normal)
  events query plain === events query actual
  disabled === Machine.checkpointMetrics normal
  Machine.metricPredicateCacheHits disabled === 0
  Machine.metricPredicateCacheMisses disabled === 0
  Machine.metricCodeCacheHits disabled === 0
  -- Nothing is memoized too: this directly constructed clause deliberately
  -- fails the compiler's local-count validation but retains legacy execution.
  fallbackBase <- load "<- notable.\np : nondet (any: <=>).\nroot : nondet (any: <=>).\nroot X <- p X, p X."
  let unsupported = Clause (Compound "p" [Var 0]) [unify (Var 0) (Atom "kept")] (-1)
      fallbackProgram = addClause unsupported fallbackBase
  fallbackQuery <- queryText "root X?"
  fallbackStart <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode fallbackProgram fallbackQuery)
  (fallback, fallbackMetrics) <- evalEither (drain fallbackStart)
  events fallbackQuery fallback === events fallbackQuery (Reference.solveQuery fallbackProgram fallbackQuery)
  values "X" fallbackQuery fallback === [Atom "kept"]
  Machine.metricPredicateCacheHits fallbackMetrics === 2
  Machine.metricPredicateCacheMisses fallbackMetrics === 0
  Machine.metricCodeCacheHits fallbackMetrics === 1
  Machine.metricCompiledActivations fallbackMetrics === 1

prop_contract_inference_table_index_and_dynamic_metadata_are_fresh :: Property
prop_contract_inference_table_index_and_dynamic_metadata_are_fresh = unit $ do
  initial <- load "<- notable.\np 1.\np 2."
  query <- queryText "p X?"
  let committing = editPred ("p", 1) (\definition -> definition
        {predInferred = (predInferred definition) {sigDet = Semidet, sigSwitch = []}}) initial
      nondeterministic = editPred ("p", 1) (\definition -> definition
        {predInferred = (predInferred definition) {sigDet = Nondet, sigSwitch = []}}) committing
  committed <- compareQuery committing query
  values "X" query committed === [IntLit 1]
  restored <- compareQuery nondeterministic query
  values "X" query restored === [IntLit 1, IntLit 2]
  reinferred <- compareQuery (inferProgram nondeterministic) query
  values "X" query reinferred === [IntLit 1, IntLit 2]
  let inputOnly = addDecl (Decl "p" (Just Nondet) [] [ArgSpec SInt ModeIn]) initial
      alternative = addDecl (Decl "p" (Just Nondet) [] [ArgSpec SInt ModeOut]) inputOnly
  inputResult <- compareQuery inputOnly query
  [problem | Reference.BranchError problem <- inputResult] === [ModeError ("p", 1) 1 (Var 0)]
  [() | Reference.Found _ <- inputResult] === []
  alternativeResult <- compareQuery alternative query
  values "X" query alternativeResult === [IntLit 1, IntLit 2]
  ground <- queryText "p 2?"
  indexOff <- evalMaybe (addDirective [Atom "noindex"] initial)
  indexedStart <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode initial ground)
  unindexedStart <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode indexOff ground)
  (indexed, indexedMetrics) <- evalEither (drain indexedStart)
  (unindexed, unindexedMetrics) <- evalEither (drain unindexedStart)
  events ground indexed === events ground unindexed
  Machine.metricPredicateCacheHits indexedMetrics === 1
  Machine.metricPredicateCacheHits unindexedMetrics === 2
  duplicates <- load "<- notable.\np : nondet (int: <=>).\np 1.\np 1.\np 2."
  _ <- compareQuery duplicates query
  let tabled = editPred ("p", 1) (\definition -> definition {predFlags = FlagTable : predFlags definition}) duplicates
  tableResult <- compareQuery tabled query
  values "X" query tableResult === [IntLit 1, IntLit 2]
  assert (any (not . Map.null . Reference.ssTables) [state | Reference.Found state <- tableResult])
  static <- load "<- notable.\nmemo kept.\nmemo : nondet (any: <=>) (any: <=>).\nroot : nondet (any: <=>).\nroot X <- memo X."
  let crossArity = editPred ("memo", 2)
        (\definition -> definition {predFlags = FlagDynamic : predFlags definition}) static
  rootQuery <- queryText "root X?"
  staticStart <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode static rootQuery)
  dynamicStart <- evalEither (Machine.startMeasuredWithBackend Machine.Bytecode crossArity rootQuery)
  (staticResult, staticMetrics) <- evalEither (drain staticStart)
  (dynamicResult, dynamicMetrics) <- evalEither (drain dynamicStart)
  events rootQuery dynamicResult === events rootQuery staticResult
  events rootQuery dynamicResult === events rootQuery (Reference.solveQuery crossArity rootQuery)
  Machine.metricDirectCalls staticMetrics === 1
  Machine.metricDirectCalls dynamicMetrics === 0
  dynamicBase <- load "<- notable.\nmemo : nondet (any: <=>) (any: <=>).\nroot : nondet unsafe (any: <=>).\nroot X <- assert (memo kept), memo X."
  _ <- compareQuery dynamicBase rootQuery
  let dynamicFlag = editPred ("memo", 2)
        (\definition -> definition {predFlags = FlagDynamic : predFlags definition}) dynamicBase
      nameFlag = addDecl (Decl "memo" Nothing [FlagDynamic] []) dynamicBase
  forM_ [dynamicFlag, nameFlag] $ \program -> do
    result <- compareQuery program rootQuery
    values "X" rootQuery result === [Atom "kept"]

prop_builtin_precedence_preserves_arity_and_outer_term_shape :: Property
prop_builtin_precedence_preserves_arity_and_outer_term_shape = unit $ do
  base <- load "<- notable.\nroot : nondet unsafe (any: <=>)."
  let shadow name count body = Clause (Compound name (map Var [0 .. count - 1])) body count
      definitions =
        [ shadow "unify" 2 [Atom "fail"], shadow "is" 2 [Atom "fail"],
          shadow "str_concat" 3 [Atom "fail"],
          shadow "write" 1 [Atom "fail"],
          shadow "str_concat" 1 [unify (Var 0) (StrLit "arity_one")],
          Clause (Atom "true") [Atom "fail"] 0,
          Clause (Compound "true" []) [Compound "write" [Atom "compound_true"]] 0,
          shadow "$cut" 1 [unify (Var 0) (Atom "ordinary")]
        ]
      withDefinitions = foldl (flip addClause) base definitions
      fixtures =
        [ ([unify (Var 0) (IntLit 7)], IntLit 7, []),
          ([Compound "is" [Var 0, Compound "plus" [IntLit 1, IntLit 2]]], IntLit 3, []),
          ([Compound "str_concat" [StrLit "a", StrLit "b", Var 0]], StrLit "ab", []),
          ([Compound "str_concat" [Var 0]], StrLit "arity_one", []),
          ([Compound "write" [Atom "visible"], unify (Var 0) (Atom "done")], Atom "done", [Reference.WriteEvent "visible"]),
          ([Atom "true", unify (Var 0) (Atom "done")], Atom "done", []),
          ([Compound "true" [], unify (Var 0) (Atom "done")], Atom "done", [Reference.WriteEvent "compound_true"]),
          ([Compound "$cut" [Var 0]], Atom "ordinary", [])
        ]
  query <- queryText "root X?"
  forM_ fixtures $ \(body, expected, output) -> do
    let program = addClause (Clause (Compound "root" [Var 0]) body 1) withDefinitions
    actual <- compareQuery program query
    values "X" query actual === [expected]
    [Reference.answerOutput (Reference.projectAnswer query state) | Reference.Found state <- actual] === [output]
    [problem | Reference.BranchError problem <- actual] === []

prop_dynamic_facts_and_fresh_ids_are_never_cached_as_results :: Property
prop_dynamic_facts_and_fresh_ids_are_never_cached_as_results = unit $ do
  program <- load $ unlines
    [ "<- notable.", "memo : dynamic.", "fresh X (box X).",
      "root : nondet unsafe (any: <=>).",
      "root X <- (assert (memo first), memo X ; assert (memo second), memo X).",
      "change : nondet unsafe (any: <=>).",
      "change X <- assert (memo first), memo Before, retract (memo Before), assert (memo second), memo X.",
      "independent Left Right <- fresh A Left, fresh B Right, A = first, B = second.",
      "p : nondet (any: <=>).", "p first.", "p second.", "p third."
    ]
  forM_ [("root X?", [Atom "first", Atom "second"]), ("change X?", [Atom "second"])] $ \(source, expected) -> do
    query <- queryText source
    actual <- compareQuery program query
    values "X" query actual === expected
  independent <- queryText "independent Left Right?"
  independentResult <- compareQuery program independent
  values "Left" independent independentResult === [Compound "box" [Atom "first"]]
  values "Right" independent independentResult === [Compound "box" [Atom "second"]]
  query <- queryText "p X?"
  start <- evalEither (Machine.startWithBackend Machine.Bytecode program query)
  first <- evalEither (Machine.resume start)
  case first of
    Machine.Yield retained next -> do
      let changed = editPred ("p", 1) (\definition -> definition
            {predClauses = IM.singleton 0 (Clause (Compound "p" [Atom "new"]) [] 0)}) program
      newResult <- compareQuery changed query
      values "X" query newResult === [Atom "new"]
      (rest, _) <- evalEither (drain next)
      (repeated, _) <- evalEither (drain next)
      values "X" query [retained] === [Atom "first"]
      values "X" query rest === [Atom "second", Atom "third"]
      events query repeated === events query rest
    _ -> failure

drainTraced :: Machine.Checkpoint -> Either Heap.HeapError ([Trace.TraceEvent], Reference.Search)
drainTraced checkpoint = do
  (trace, step) <- Machine.resumeTraced checkpoint
  case step of
    Machine.Finished -> pure (trace, [])
    Machine.Yield item next -> do
      (laterTrace, later) <- drainTraced next
      pure (trace ++ laterTrace, item : later)

prop_source_maps_files_and_explicit_fuel_follow_program_snapshots :: Property
prop_source_maps_files_and_explicit_fuel_follow_program_snapshots = unit $ do
  let source = "<- notable.\nroot : nondet unsafe (str: =>).\nroot Text <- read_file \"virtual.txt\" Text."
  loaded <- load source
  oldLocations <- evalEither (parseLocatedFile "old.infera" source)
  newLocations <- evalEither (parseLocatedFile "new.infera" ("\n\n" ++ source))
  let old = (addFiles [("virtual.txt", "old")] loaded) {progSources = Trace.sourceMap oldLocations}
      new = (addFiles [("virtual.txt", "new")] old) {progSources = Trace.sourceMap newLocations}
  query <- queryText "root Text?"
  retained <- evalEither (Machine.startWithBackend Machine.Bytecode old query)
  (before, _) <- evalEither (drain retained)
  values "Text" query before === [StrLit "old"]
  forM_ [(old, "old", "old.infera"), (new, "new", "new.infera")] $ \(program, text, file) -> do
    actual <- compareQuery program query
    values "Text" query actual === [StrLit text]
    compiled <- evalEither (Machine.startTracedWithBackend Machine.Bytecode program query)
    interpreted <- evalEither (Machine.startTracedWithBackend Machine.Interpreted program query)
    (trace, found) <- evalEither (drainTraced compiled)
    (oldTrace, expected) <- evalEither (drainTraced interpreted)
    trace === oldTrace
    events query found === events query expected
    assert (file `elem` [spanFile site | event <- trace, Just site <- [Trace.traceSpan event]])
    forM_ [0, 1, 2, 3] $ \fuel -> do
      let environment = Reference.mkEnv program
          state = Reference.initialState (queryNVars query)
          reference = Reference.solveGoals environment fuel state (queryGoals query)
      forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
        initial <- evalEither (Machine.startGoalsWithBackend backend environment fuel state (queryGoals query))
        (foundFuel, _) <- evalEither (drain initial)
        events query foundFuel === events query reference
        rawStores foundFuel === rawStores reference
  (again, _) <- evalEither (drain retained)
  events query again === events query before

prop_changed_clp_plans_preserve_full_store_and_startup_aliases :: Property
prop_changed_clp_plans_preserve_full_store_and_startup_aliases = unit $ do
  old <- load $ unlines
    [ "<- notable.", "step : nondet (int: <=>) (int: <=>).", "step X Y <- Y #= X + 1.",
      "root : nondet (any: <=>).",
      "root List <- [X,Y] in 1..3, step X Y, findall (pair X Y) (label [X,Y]) List, label [X,Y]."
    ]
  let changedClause = Clause (Compound "step" [Var 0, Var 1])
        [Compound "int_eq" [Var 1, Compound "plus" [Var 0, IntLit 2]]] 2
      new = editPred ("step", 2) (\definition -> definition
        {predClauses = IM.singleton 0 changedClause}) old
      pair a b = Compound "pair" [IntLit a, IntLit b]
  query <- queryText "root List?"
  oldResult <- compareQuery old query
  newResult <- compareQuery new query
  values "List" query oldResult === replicate 2 (mkList [pair 1 2, pair 2 3] Nothing)
  values "List" query newResult === [mkList [pair 1 3] Nothing]
  forM_ [(old, oldResult), (new, newResult)] $ \(program, actual) -> do
    rawStores actual === rawStores (Reference.solveQuery program query)
    rawStores actual === rawStores (Machine.solveQueryWithBackend Machine.Interpreted program query)
  let aliases = emptyStore {stSubst = IM.fromList [(0, Var 1), (2, Var 0)]}
  store <- case addDomains [Var 0, Var 3] (Fin 1) (Fin 3) aliases of
    Right (Just accepted) -> pure accepted
    other -> annotateShow other >> failure
  let goals = [Compound "step" [Var 0, Var 3], Compound "label" [mkList [Var 0, Var 3] Nothing]]
      aliasQuery = Query goals [("X", 0), ("Alias", 1), ("Other", 2), ("Y", 3)] 4
      state = (Reference.initialState 4) {Reference.ssStore = store}
  forM_ [old, new] $ \program -> do
    let environment = Reference.mkEnv program
        reference = Reference.solveGoals environment 4 state goals
    forM_ [Machine.Interpreted, Machine.Bytecode] $ \backend -> do
      initial <- evalEither (Machine.startGoalsWithBackend backend environment 4 state goals)
      (actual, _) <- evalEither (drain initial)
      events aliasQuery actual === events aliasQuery reference
      rawStores actual === rawStores reference

machineCacheGroup :: Group
machineCacheGroup = Group "predicate cache and dispatch snapshots"
  [ ("generated exact source witnesses and immutable cache versions", prop_generated_exact_witnesses_and_immutable_cache_versions),
    ("generated direct record edits and retained program snapshots", prop_generated_direct_record_edits_and_retained_programs),
    ("exact float constructor and cached fallback witnesses", prop_exact_float_constructor_and_fallback_witnesses),
    ("selected-only lazy plans and scope memoization", prop_selected_only_lazy_plans_and_scope_memoization),
    ("contracts inference table index and dynamic metadata are fresh", prop_contract_inference_table_index_and_dynamic_metadata_are_fresh),
    ("builtin precedence preserves arity and outer term shape", prop_builtin_precedence_preserves_arity_and_outer_term_shape),
    ("dynamic facts and fresh logical IDs are never cached as results", prop_dynamic_facts_and_fresh_ids_are_never_cached_as_results),
    ("source maps files and explicit fuel follow program snapshots", prop_source_maps_files_and_explicit_fuel_follow_program_snapshots),
    ("changed CLP plans preserve full stores and accepted startup aliases", prop_changed_clp_plans_preserve_full_store_and_startup_aliases)
  ]
