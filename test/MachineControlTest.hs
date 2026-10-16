{-# LANGUAGE OverloadedStrings #-}

-- The control machine is an opt-in execution path. Compare its ordered stream
-- with the current resolver, retaining duplicates and every issue. Canonicalize
-- a whole answer at once so aliases between different bindings stay visible.
module MachineControlTest (machineControlGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Engine as Reference
import Infera.CLP
import Infera.Error
import Infera.Infer (inferProgram)
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.Heap as Heap
import Infera.Program
import Infera.Syntax
import Infera.Unify (canonicalize, emptySubst)

data ObservedTerm
  = OAtom String | OVar VarId | OInt Integer | OFloat Word64
  | OChar Char | OString String | OCompound String [ObservedTerm]
  deriving (Eq, Show)

observeTerm :: Term -> ObservedTerm
observeTerm term = case term of
  Atom value -> OAtom value
  Var value -> OVar value
  IntLit value -> OInt value
  FloatLit value -> OFloat (castDoubleToWord64 value)
  CharLit value -> OChar value
  StrLit value -> OString value
  Compound name arguments -> OCompound name (map observeTerm arguments)

-- Named query variables have stable public identities. Seed canonicalization
-- with all of them, rather than accidentally equating X = Y with X = Z.
canonicalTerms :: Query -> [Term] -> [Term]
canonicalTerms query terms = case fst (canonicalize emptySubst combined) of
  Compound _ roots -> drop (length names) roots
  _ -> error "canonicalizing a compound changed its constructor"
  where
    names = map (Var . snd) (queryNames query)
    combined = Compound "$observations" (names ++ terms)

normalizeError :: Query -> SolveError -> SolveError
normalizeError query err = case err of
  InstantiationError term -> InstantiationError (canonical term)
  ExpectedInteger term -> ExpectedInteger (canonical term)
  ExpectedNumber term -> ExpectedNumber (canonical term)
  ModeError key index term -> ModeError key index (canonical term)
  OutputModeError key index term -> OutputModeError key index (canonical term)
  SortError key index sort term -> SortError key index sort (canonical term)
  CLPTypeError term -> CLPTypeError (canonical term)
  UnboundedDomain term -> UnboundedDomain (canonical term)
  TypeError description term -> TypeError description (canonical term)
  other -> other
  where
    canonical term = case canonicalTerms query [term] of
      [result] -> result
      _ -> error "canonicalization changed the number of roots"

data Event
  = AnswerEvent [(String, ObservedTerm)] [String] [Reference.OutputEvent]
  | ExhaustedEvent
  | ErrorEvent String
  | CutEvent Int
  | IncompleteEvent ObservedTerm
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
            bindings = Reference.answerBindings answer
            terms = map observeTerm (canonicalTerms query (map snd bindings))
         in AnswerEvent (zip (map fst bindings) terms)
              (Reference.answerResiduals answer) (Reference.answerOutput answer)
      Reference.BranchExhausted -> ExhaustedEvent
      Reference.BranchError err -> ErrorEvent (show (normalizeError query err))
      Reference.CutMarker barrier -> CutEvent barrier
      Reference.ConsumedIncomplete key ->
        IncompleteEvent (observeTerm (fst (canonicalize emptySubst key)))

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load source = annotate source >> evalEither (Reference.loadProgramText source)

queryText :: String -> PropertyT IO Query
queryText text = annotate text >> evalEither (parseQuery text)

compareQuery :: Program -> Query -> PropertyT IO Reference.Search
compareQuery program query = do
  let actual = Machine.solveQuery program query
  observe query actual === observe query (Reference.solveQuery program query)
  pure actual

compareSource :: String -> String -> PropertyT IO Reference.Search
compareSource source text = do
  program <- load source
  query <- queryText text
  compareQuery program query

expectAnswers :: Query -> Reference.Search -> [String] -> PropertyT IO ()
expectAnswers query items expected = do
  [Reference.showAnswer (Reference.projectAnswer query state)
    | Reference.Found state <- items] === expected
  [show err | Reference.BranchError err <- items] === []
  [() | Reference.BranchExhausted <- items] === []

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

-- No recursion, builtins or reference adapters are needed by these programs:
-- p2 calls p1, p1 calls p0, and each level has ordinary indexed clauses.
genData :: Gen Term
genData = Gen.choice
  [ Var <$> Gen.int (Range.linear 0 2),
    Atom <$> Gen.element ["a", "b", "c"],
    IntLit <$> Gen.integral (Range.linear (-1) 2),
    Compound "pair" <$> sequence
      [Var <$> Gen.int (Range.linear 0 2), Var <$> Gen.int (Range.linear 0 2)]
  ]

genClause :: Int -> Gen Clause
genClause level = do
  left <- genData
  right <- genData
  extra <- Gen.choice
    [ pure [],
      pure [Compound "unify" [Var 0, Var 1]],
      pure [Compound ";" [Atom "true", Atom "true"]],
      pure [Compound ";" [Atom "fail", Atom "true"]],
      pure [Atom "!"],
      pure [Atom "!", Atom "fail"]
    ]
  body <- if level == 0 then pure extra else do
    a <- genData
    b <- genData
    pure (Compound ("p" ++ show (level - 1)) [a, b] : extra)
  pure (Clause (Compound ("p" ++ show level) [left, right]) body 3)

genAcyclicProgram :: Gen Program
genAcyclicProgram = do
  levels <- mapM (\level -> Gen.list (Range.linear 1 4) (genClause level)) [0 .. 2]
  indexed <- Gen.bool
  pure . inferProgram . buildProgram $
    TLDirective [Atom (if indexed then "index" else "noindex")]
      : [TLDecl (Decl ("p" ++ show level) Nothing [FlagUnsafe] []) | level <- [0 :: Int .. 2]]
      ++ map TLClause (concat levels)

prop_acyclic_native_programs :: Property
prop_acyclic_native_programs = withTests 300 . property $ do
  program <- forAll genAcyclicProgram
  argument <- forAll (Gen.element [Var 0, Atom "a", IntLit 1, Compound "pair" [Var 0, Var 0]])
  let query = Query [Compound "p2" [argument, Var 1]] [("X", 0), ("Y", 1)] 2
  _ <- compareQuery program query
  pure ()

genControl :: Int -> Gen Term
genControl depth = Gen.frequency $
  [(5, leaf)] ++ if depth <= 0 then [] else
    [ (2, Compound "," <$> sequence [child, child]),
      (2, Compound ";" <$> sequence [child, child])
    ]
  where
    child = genControl (depth - 1)
    leaf = Gen.choice
      [ pure (Atom "true"), pure (Atom "fail"), pure (Atom "!"),
        pure (Compound "pick" [Var 0]),
        pure (Compound "pick" [Var 1]),
        pure (Compound "unify" [Var 0, Var 1]),
        Compound "unify" <$> sequence [pure (Var 0), genData],
        pure (Atom "unknown"),
        pure (Var 2)
      ]

prop_generated_control_streams :: Property
prop_generated_control_streams = withTests 300 . property $ do
  goal <- forAll (genControl 3)
  let program = inferProgram (buildProgram
        [TLClause (Clause (Compound "pick" [IntLit value]) [] 0) | value <- [1, 1, 2]])
      query = Query [goal] [("X", 0), ("Y", 1), ("Goal", 2)] 3
  _ <- compareQuery program query
  pure ()

prop_order_aliases_and_failed_heads :: Property
prop_order_aliases_and_failed_heads = unit $ do
  program <- load $ unlines
    [ "p (pair X X) first.",
      "p (pair a b) second.",
      "p (pair a b) second.",
      "shared (pair A B) (pair B A)."
    ]
  query <- queryText "p (pair a b) Result?"
  items <- compareQuery program query
  expectAnswers query items ["Result = second", "Result = second"]
  aliases <- queryText "shared X Y?"
  shared <- compareQuery program aliases
  observe aliases shared ===
    [AnswerEvent [("X", OCompound "pair" [OVar 2, OVar 3]),
                  ("Y", OCompound "pair" [OVar 3, OVar 2])] [] []]
  distinct <- queryText "X = Y?"
  _ <- compareQuery program distinct
  pure ()

prop_cut_failure_and_boundaries :: Property
prop_cut_failure_and_boundaries = unit $ do
  program <- load $ unlines
    [ "pick 1.", "pick 2.",
      "local : unsafe.",
      "local X <- pick X, !, fail.",
      "local fallback.",
      "nested : unsafe.",
      "nested X <- (pick X, ! ; X = fallback)."
    ]
  forM_
    [ "local X?", "(pick X, !, fail ; X = fallback)?", "nested X?",
      "call (pick X, !), pick Y?", "once (pick X, !), pick Y?",
      "(call (pick X, !, fail) ; X = fallback)?",
      "(not (pick X, !, fail) ; X = fallback)?"
    ] $ \text -> queryText text >>= compareQuery program >> pure ()

prop_contracts_before_commit :: Property
prop_contracts_before_commit = unit $ do
  program <- load $ unlines
    [ "p : semidet (int: =>).", "p X.", "p 7.", "p 8.",
      "det_bad : det (int: =>).", "det_bad X.", "det_bad X <- fail.",
      "multi_bad : multi (int: =>).", "multi_bad X.",
      "multi_fail : multi (any: <=>).", "multi_fail _ <- fail.",
      "det_fail : det (any: <=>).", "det_fail _ <- fail.",
      "input : semidet (int: <=).", "input _."
    ]
  forM_ ["p X?", "det_bad X?", "multi_bad X?", "multi_fail X?", "det_fail X?",
          "input X?", "input atom?"] $ \text ->
    queryText text >>= compareQuery program >> pure ()
  query <- queryText "p X?"
  let events = observe query (Machine.solveQuery program query)
  length [() | ErrorEvent _ <- events] === 1
  [Reference.showAnswer (Reference.projectAnswer query state)
    | Reference.Found state <- Machine.solveQuery program query] === ["X = 7"]

prop_fuel_sibling_fairness :: Property
prop_fuel_sibling_fairness = unit $ do
  program <- load $ unlines
    [ "<- notable.", "loop X <- loop X.", "pick 1.", "pick 2.",
      "outer X <- loop X.", "outer sibling."
    ]
  let environment = Reference.mkEnv program
      state = Reference.initialState 1
      query = Query [] [("X", 0)] 1
  forM_ [0 .. 4] $ \fuel -> forM_
    [ [Compound ";" [Compound "loop" [Var 0], Compound "pick" [Var 0]]],
      [Compound "outer" [Var 0]],
      [Compound "pick" [Var 0], Compound "pick" [Var 0]]
    ] $ \goals -> do
      annotateShow (fuel, goals)
      observe query (Machine.solveGoals environment fuel state goals)
        === observe query (Reference.solveGoals environment fuel state goals)

prop_repeated_interleaved_resume :: Property
prop_repeated_interleaved_resume = unit $ do
  program <- load $ unlines
    ["pick (pair A A).", "pick first.", "pick second.", "pick second."]
  query <- queryText "pick X, (Y = X ; Y = retained)?"
  initial <- evalEither (Machine.start program query)
  first <- evalEither (Machine.resume initial)
  case first of
    Machine.Finished -> failure
    Machine.Yield retained next -> do
      let before = observe query [retained]
      -- Force the first observation before resuming. Leaving it lazy would
      -- compare two observations both first evaluated after later writes.
      _ <- evalIO (evaluate (length (show before)))
      branch <- evalEither (drain next)
      other <- evalEither (drain initial)
      repeated <- evalEither (drain next)
      observe query branch === observe query repeated
      observe query other === observe query (Reference.solveQuery program query)
      -- Reading the retained Found after later branches have rebound the
      -- same heap slots must still see the original aliases and terms.
      observe query [retained] === before
      observe query (retained : branch) === observe query other
      again <- evalEither (Machine.resume initial)
      case again of
        Machine.Finished -> failure
        Machine.Yield retainedAgain following -> do
          observe query [retainedAgain] === before
          followingItems <- evalEither (drain following)
          observe query followingItems === observe query branch
  -- call/1 enters the reference adapter with an unbounded source generator.
  -- Observing a small prefix must not traverse its remaining answer stream.
  lazyProgram <- load $ unlines
    ["p : nondet notable (any: <=>).", "p first.", "p X <- p X."]
  lazyQuery <- queryText "call (p X)?"
  lazyInitial <- evalEither (Machine.start lazyProgram lazyQuery)
  firstPrefix <- evalEither (prefix 3 lazyInitial)
  repeatedPrefix <- evalEither (prefix 3 lazyInitial)
  observe lazyQuery firstPrefix
    === observe lazyQuery (take 3 (Reference.solveQuery lazyProgram lazyQuery))
  observe lazyQuery repeatedPrefix === observe lazyQuery firstPrefix
  expectAnswers lazyQuery firstPrefix ["X = first", "X = first", "X = first"]

prop_checkpointed_adapter_state :: Property
prop_checkpointed_adapter_state = unit $ do
  -- Every adapter must carry the entire Store/output/table/dynamic snapshot,
  -- not merely reconstruct a substitution and silently drop other fields.
  forM_
    [ ("", "X in 1..3, Y in 1..3, X #< Y, (X = 1 ; X = 2), label [X, Y]?"),
      ("", "X != Y, (X = a ; X = b), Y = a?"),
      ("", "(write first, X = 1 ; write second, X = 2), nl?"),
      (unlines ["edge a b.", "edge b c.", "edge c a.",
                 "path X Y <- path X Z, edge Z Y.", "path X Y <- edge X Y."],
        "path a X, (Y = X ; Y = branch)?"),
      ("fact : dynamic.",
        "assert (fact seed), (assert (fact left), fact X ; assert (fact right), fact X)?")
    ] $ \(source, text) -> do
      program <- load source
      query <- queryText text
      initial <- evalEither (Machine.start program query)
      first <- evalEither (drain initial)
      second <- evalEither (drain initial)
      observe query first === observe query second
      observe query first === observe query (Reference.solveQuery program query)

prop_findall_variable_sharing :: Property
prop_findall_variable_sharing = unit $ do
  -- The current resolver's findall shares entry variables. A machine migration
  -- must not quietly introduce fresh-copy semantics as a side effect.
  forM_
    [ "findall X true L, X = shared?",
      "findall (pair X Y) (Y = X ; true) L, X = shared?",
      "X = (box Y), findall X true L, Y = shared?",
      "findall X fail L?"
    ] $ \text -> do
      _ <- compareSource "" text
      pure ()

prop_nan_adapter_boundary :: Property
prop_nan_adapter_boundary = unit $ do
  let nan = FloatLit (0 / 0)
      query = Query
        [ Compound "unify" [Var 0, nan],
          Compound "nonvar" [Var 0],
          Compound ";"
            [Compound "unify" [Var 0, Var 0], Compound "unify" [Var 1, Atom "fallback"]]
        ] [("X", 0), ("Y", 1)] 2
  _ <- compareQuery emptyProgram query
  pure ()

prop_shallow_control_syntax :: Property
prop_shallow_control_syntax = unit $ do
  -- The resolver recognizes if/then/else from the original outer syntax.
  -- A variable in the left disjunct that later walks to -> is still an
  -- ordinary disjunction; eagerly dereferencing every child changes control.
  let conditional = Compound "->" [Atom "true", Atom "fail"]
      query = Query
        [Compound "unify" [Var 0, conditional], Compound ";" [Var 0, Atom "true"]]
        [("Goal", 0)] 1
  items <- compareQuery emptyProgram query
  length [() | Reference.Found _ <- items] === 1
  let rawCut = Query
        [ Compound "unify" [Var 0, Compound "$cut" [IntLit (-1)]],
          Compound ";" [Var 0, Atom "true"]
        ] [("Goal", 0)] 1
  _ <- compareQuery emptyProgram rawCut
  forM_
    [ "G = (H ; X = otherwise), H = (true -> X = then), call G?",
      "(G = (true -> X = then), (G ; X = otherwise))?"
    ] $ \text -> do
      parsed <- queryText text
      answers <- compareQuery emptyProgram parsed
      length [() | Reference.Found _ <- answers] === 2
  forM_
    [ ("G = (H ; X = otherwise), H = (true -> X = then), once (G, X = otherwise)?", 1),
      ("G = (H ; X = otherwise), H = (true -> X = then), not (G, X = otherwise)?", 0),
      ("G = (H ; X = otherwise), H = (true -> X = then), findall X G L?", 1)
    ] $ \(text, count) -> do
      parsed <- queryText text
      answers <- compareQuery emptyProgram parsed
      length [() | Reference.Found _ <- answers] === count
  callerCutProgram <- load $ unlines
    ["run : unsafe.", "run G first <- G.", "run _ second."]
  let callerCutQuery = Query
        [Compound ";" [Compound "run" [Atom "!", Var 0],
          Compound "unify" [Var 0, Atom "otherwise"]]] [("X", 0)] 1
  callerCutAnswers <- compareQuery callerCutProgram callerCutQuery
  expectAnswers callerCutQuery callerCutAnswers ["X = first"]
  -- A later cut owned by run masks the earlier caller-owned marker while
  -- the first result's continuation is running. The outer alternative then
  -- survives even though run's own second clause is pruned.
  forM_ ["G", "forward G"] $ \invocation -> do
    twoCutProgram <- load $ unlines
      [ "run : nondet unsafe (any: <=>) (any: <=>).",
        "forward : nondet unsafe (any: <=>).", "forward G <- G.",
        "run G first <- " ++ invocation ++ ", !.", "run _ second."
      ]
    twoCutAnswers <- compareQuery twoCutProgram callerCutQuery
    expectAnswers callerCutQuery twoCutAnswers ["X = first", "X = otherwise"]
  -- A committing call takes only its first checked solution. Its adapter
  -- drops a foreign cut beyond that solution (or drops a bare marker if it
  -- never finds a solution), so the caller's disjunction remains available.
  forM_ [(Semidet, "semidet"), (Det, "det")] $ \(determinism, declaration) -> do
    -- The forward variant crosses a noncommitting return before reaching
    -- the committing run activation; that return must preserve its guard.
    forM_ ["G", "forward G"] $ \invocation -> do
      let declarations =
            [ "run : " ++ declaration ++ " unsafe (any: <=>) (any: <=>).",
              "forward : nondet unsafe (any: <=>).", "forward G <- G."
            ]
      committingProgram <- load $ unlines (declarations ++
        ["run G first <- " ++ invocation ++ ".", "run _ second."])
      committed <- compareQuery committingProgram callerCutQuery
      expectAnswers callerCutQuery committed ["X = first", "X = otherwise"]
      failingProgram <- load $ unlines (declarations ++
        ["run G first <- " ++ invocation ++ ", fail.", "run _ second."])
      failed <- compareQuery failingProgram callerCutQuery
      let fallback = AnswerEvent [("X", OAtom "otherwise")] [] []
          expected = case determinism of
            Det -> [ErrorEvent (show (DetError ("run", 2) Det 0)), fallback]
            _ -> [fallback]
      observe callerCutQuery failed === expected
  -- Only a literal integer child makes the internal cut form special.
  -- A raw variable stays an ordinary $cut/1 call even after it is bound.
  let variableOwner = Query
        [ Compound "unify" [Var 0, IntLit (-1)],
          Compound ";" [Compound "$cut" [Var 0], Atom "true"]
        ] [("Owner", 0)] 1
  variableOwnerItems <- compareQuery emptyProgram variableOwner
  observe variableOwner variableOwnerItems ===
    [ErrorEvent (show (UnknownPredicate ("$cut", 1))),
      AnswerEvent [("Owner", OInt (-1))] [] []]
  pure ()

must :: Show err => ST s (Either err value) -> ST s value
must action = action >>= either (error . show) pure

prop_bridge_sparse_roots_and_full_store :: Property
prop_bridge_sparse_roots_and_full_store = unit $ do
  let constraint = CDiseq (Var 1000) (Atom "excluded")
      store = emptyStore
        { stDomains = IM.singleton 1000 (Domain (Fin 1) (Fin 9) (Set.singleton 4)),
          stConstraints = [constraint],
          stWatched = IS.fromList [1000, 9000],
          stConstraintMap = IM.singleton 42 constraint,
          stDependencies = IM.singleton 1000 (IS.singleton 42),
          stPending = IS.singleton 42,
          stDirtyVars = IS.fromList [1000, 9000],
          stNextConstraint = 43,
          stConstraintCount = 1
        }
      state = (Reference.initialState 0)
        { Reference.ssStore = store,
          Reference.ssOutput = [Reference.WriteEvent "retained"],
          Reference.ssOutLen = 1,
          Reference.ssDynamic = Map.singleton ("fact", 1) [(Compound "fact" [Var 1000], 1)]
        }
      (terms, exportedStore, output, outLen, dynamic) = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [2, 1000, 9000])
        (bindings', addresses) <- must (Bridge.importTerms heap bindings
          [Var 2, Var 1000, Var 9000, Atom "ground", Compound "pair" [Var 1000, Var 1000]])
        case addresses of
          [early, _, later, ground, pair] -> do
            _ <- must (Heap.unify heap early ground)
            _ <- must (Heap.unify heap later pair)
            observedRoots <- must (Bridge.exportTerms heap bindings' addresses)
            exported <- must (Bridge.exportState heap bindings' state)
            pure (observedRoots, Reference.ssStore exported, Reference.ssOutput exported,
              Reference.ssOutLen exported, Reference.ssDynamic exported)
          _ -> error "bridge changed the number of imported roots"
  terms === [Atom "ground", Var 1000, Compound "pair" [Var 1000, Var 1000],
             Atom "ground", Compound "pair" [Var 1000, Var 1000]]
  exportedStore {stSubst = emptySubst} === store
  stSubst exportedStore === IM.fromList
    [(2, Atom "ground"), (9000, Compound "pair" [Var 1000, Var 1000])]
  output === Reference.ssOutput state
  outLen === Reference.ssOutLen state
  dynamic === Reference.ssDynamic state

prop_bridge_sync_is_atomic :: Property
prop_bridge_sync_is_atomic = unit $ do
  let state = (Reference.initialState 2) {Reference.ssStore = emptyStore
        {stSubst = IM.fromList [(0, Atom "new"), (1, Atom "incompatible")]}}
      (rejected, before, after, sizes) = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0, 1])
        (bindings', addresses) <- must (Bridge.importTerms heap bindings [Var 0, Var 1, Atom "seed"])
        case addresses of
          [first, second, scalar] -> do
            _ <- must (Heap.unify heap second scalar)
            beforeSync <- must (Bridge.exportTerms heap bindings' [first, second])
            initialHeap <- Heap.heapSize heap
            initialTrail <- Heap.trailSize heap
            result <- Bridge.syncState heap bindings' state
            afterSync <- must (Bridge.exportTerms heap bindings' [first, second])
            finalHeap <- Heap.heapSize heap
            finalTrail <- Heap.trailSize heap
            pure (case result of Left Heap.IncompatibleBindings -> True; _ -> False,
              beforeSync, afterSync, (initialHeap, initialTrail, finalHeap, finalTrail))
          _ -> error "bridge changed the number of imported roots"
  assert rejected
  before === [Var 0, Atom "seed"]
  after === before
  case sizes of
    (initialHeap, initialTrail, finalHeap, finalTrail) -> do
      finalHeap === initialHeap
      finalTrail === initialTrail

prop_bridge_frozen_sync_and_nan :: Property
prop_bridge_frozen_sync_and_nan = unit $ do
  let nan = FloatLit (0 / 0)
      compound child = Compound "f" [child, nan]
      state value = (Reference.initialState 3) {Reference.ssStore = emptyStore
        {stSubst = IM.fromList [(0, compound (Atom value)), (1, Atom value), (2, nan)]}}
      (first, second, repeated, parent) = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0, 1, 2])
        (bindings', roots) <- must (Bridge.importTerms heap bindings
          [Var 0, Var 1, Var 2, compound (Var 1), nan])
        case roots of
          [root, child, scalarRoot, structured, scalar] -> do
            _ <- must (Heap.unify heap root structured)
            _ <- must (Heap.unify heap scalarRoot scalar)
            frozen <- Heap.freezeHeap heap
            let branch value = do
                  resumed <- Heap.thawHeap frozen
                  nextBindings <- must (Bridge.syncState resumed bindings' (state value))
                  map observeTerm <$> must (Bridge.exportTerms resumed nextBindings [root, child, scalarRoot])
            firstBranch <- branch "first"
            secondBranch <- branch "second"
            repeatedBranch <- branch "first"
            parentRoots <- map observeTerm <$> must (Bridge.exportTerms heap bindings' [root, child, scalarRoot])
            pure (firstBranch, secondBranch, repeatedBranch, parentRoots)
          _ -> error "bridge changed the number of imported roots"
      expected value = map observeTerm [compound (Atom value), Atom value, nan]
  first === expected "first"
  second === expected "second"
  repeated === first
  parent === map observeTerm [compound (Var 1), Var 1, nan]

machineControlGroup :: Group
machineControlGroup = Group "machine control"
  [ ("acyclic_native_programs", prop_acyclic_native_programs),
    ("generated_control_streams", prop_generated_control_streams),
    ("order_aliases_and_failed_heads", prop_order_aliases_and_failed_heads),
    ("cut_failure_and_boundaries", prop_cut_failure_and_boundaries),
    ("contracts_before_commit", prop_contracts_before_commit),
    ("fuel_sibling_fairness", prop_fuel_sibling_fairness),
    ("repeated_interleaved_resume", prop_repeated_interleaved_resume),
    ("checkpointed_adapter_state", prop_checkpointed_adapter_state),
    ("findall_variable_sharing", prop_findall_variable_sharing),
    ("nan_adapter_boundary", prop_nan_adapter_boundary),
    ("shallow_control_syntax", prop_shallow_control_syntax),
    ("bridge_sparse_roots_and_full_store", prop_bridge_sparse_roots_and_full_store),
    ("bridge_sync_is_atomic", prop_bridge_sync_is_atomic),
    ("bridge_frozen_sync_and_nan", prop_bridge_frozen_sync_and_nan)
  ]
