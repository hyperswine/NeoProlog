{-# LANGUAGE OverloadedStrings #-}

-- Reclamation follows logical roots rather than the historical fresh-ID
-- range. These generated models deliberately retain raw control syntax and
-- noncanonical alias representatives, alongside complete CLP metadata.
module MachineReclaimTest (machineReclaimGroup) where

import Control.Monad (forM)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax
import Infera.Unify (deepWalk, emptySubst)

must :: Show err => ST s (Either err a) -> ST s a
must action = action >>= either (error . show) pure

single :: [a] -> a
single [value] = value
single _ = error "bridge changed root count"

data Fixture = Fixture
  { fixtureState :: Reference.SolverState,
    fixtureProtected :: [VarId],
    fixtureAllIds :: [VarId],
    fixtureLiveIds :: [VarId],
    fixtureRaw :: [Term],
    fixtureFree :: VarId
  }

-- Obtain an opaque table through the public resolver rather than duplicating
-- its private representation. This closed seed is shared by all fixtures.
tableState :: Reference.SolverState
tableState = case (Reference.loadProgramText "seed : table.\nseed a.", parseQuery "seed X?") of
  (Right program, Right query) ->
    case [state | Reference.Found state <- Reference.solveQuery program query] of
      state : _ | not (Map.null (Reference.ssTables state)) -> state
      _ -> error "tabled seed did not produce a completed table"
  _ -> error "invalid table fixture source"

fixture :: Int -> Int -> Int -> Int -> Bool -> Int -> Integer -> Fixture
fixture base stride aliasCount deadCount reversed depth fresh = Fixture
  state [protected] (liveIds ++ deadIds ++ [base + 90000]) liveIds syntax
  finalAlias
  where
    protected = base
    control = base + 1000
    ordered = [base + 100 + stride * i | i <- [0 .. aliasCount]]
    aliases = if reversed then reverse ordered else ordered
    firstAlias = base + 100 + if reversed then stride * aliasCount else 0
    finalAlias = base + 100 + if reversed then 0 else stride * aliasCount
    metadata = [base + 2000 + stride * i | i <- [0 .. 5]]
    domainId = metadata !! 0
    residualId = metadata !! 1
    mapId = metadata !! 2
    watchedId = metadata !! 3
    dirtyId = metadata !! 4
    dependencyId = metadata !! 5
    deadIds = [base + 20000 + stride * i | i <- [0 .. deadCount - 1]]
    liveIds = protected : control : aliases ++ metadata
    wrap 0 term = term
    wrap n term = Compound "box" [term, Var firstAlias, wrap (n - 1) (Var control)]
    protectedTerm = wrap depth (Compound "pair" [Var firstAlias, Var control])
    liveSubst = IM.fromList $
      [(protected, protectedTerm), (control, Compound "->" [Atom "true", Atom "chosen"])]
        ++ zip aliases (map Var (drop 1 aliases))
    deadSubst = IM.fromList [(v, Atom ("discarded_constant_" ++ show v)) | v <- deadIds]
    residual = CDiseq (Var residualId) (Atom "excluded")
    mapped = CReified RelLe (Var mapId) (IntLit 7) (Var watchedId)
    store = emptyStore
      { stSubst = IM.union liveSubst deadSubst,
        stDomains = IM.singleton domainId (Domain (Fin 1) (Fin 9) (Set.singleton 4)),
        stConstraints = [residual],
        stWatched = IS.singleton watchedId,
        stConstraintMap = IM.singleton 42 mapped,
        stDependencies = IM.singleton dependencyId (IS.singleton 42),
        stPending = IS.singleton 42,
        stDirtyVars = IS.singleton dirtyId,
        stNextConstraint = 43,
        stConstraintCount = 1
      }
    -- Table/fact variables are canonical local names, not logical heap roots.
    state = (Reference.initialState 0)
      { Reference.ssStore = store,
        Reference.ssFresh = fromInteger fresh,
        Reference.ssOutput = [Reference.WriteEvent "kept", Reference.NewlineEvent],
        Reference.ssOutLen = 2,
        Reference.ssTables = Reference.ssTables tableState,
        Reference.ssDynamic = Map.singleton ("fact", 1) [(Compound "fact" [Var 0], 1)]
      }
    syntax =
      [ Compound "use" [Var protected, Var firstAlias],
        Compound ";" [Var control, Atom "fallback"],
        Var firstAlias
      ]

genFixture :: Gen Fixture
genFixture = fixture
  <$> Gen.int (Range.linear 1 500)
  <*> Gen.int (Range.linear 3 30)
  <*> Gen.int (Range.linear 1 7)
  <*> Gen.int (Range.linear 10 50)
  <*> Gen.bool
  <*> Gen.int (Range.linear 0 3)
  <*> Gen.integral (Range.linear 100000 1000000)

sameMetadata :: Reference.SolverState -> Reference.SolverState -> PropertyT IO ()
sameMetadata actual expected = do
  (Reference.ssStore actual) {stSubst = emptySubst}
    === (Reference.ssStore expected) {stSubst = emptySubst}
  Reference.ssFresh actual === Reference.ssFresh expected
  Reference.ssOutput actual === Reference.ssOutput expected
  Reference.ssOutLen actual === Reference.ssOutLen expected
  show (Reference.ssTables actual) === show (Reference.ssTables expected)
  Reference.ssDynamic actual === Reference.ssDynamic expected

prop_generated_raw_roots_and_complete_metadata :: Property
prop_generated_raw_roots_and_complete_metadata = withTests 200 . property $ do
  sample <- forAllWith (show . fixtureLiveIds) genFixture
  let initial = fixtureState sample
      substitution = stSubst (Reference.ssStore initial)
      syntax = fixtureRaw sample
      liveIds = IS.fromList (fixtureLiveIds sample)
      expectedSubst = IM.filterWithKey (\v _ -> IS.member v liveIds) substitution
      expectedTerms = map (deepWalk substitution) syntax
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap (fixtureAllIds sample))
        synchronized <- must (Bridge.syncState heap bindings initial {Reference.ssFresh = 0})
        (imported, roots) <- must (Bridge.importTerms heap synchronized syntax)
        oldInterns <- Heap.internSize heap
        frozen <- Heap.freezeHeap heap
        (nextHeap, nextBindings, compacted, nextRoots) <- must
          (Bridge.rebuild heap imported (fixtureProtected sample) initial roots)
        raw <- must (Bridge.exportRawTerms nextHeap nextBindings nextRoots)
        terms <- must (Bridge.exportTerms nextHeap nextBindings nextRoots)
        trail <- Heap.trailSize nextHeap
        newInterns <- Heap.internSize nextHeap
        invalidated <- forM roots $ \address -> do
          viewed <- Heap.view nextHeap address
          pure $ case viewed of Left (Heap.InvalidAddress _) -> True; _ -> False
        oldTerms <- must (Bridge.exportTerms heap imported roots)
        resumed <- Heap.thawHeap frozen
        frozenTerms <- must (Bridge.exportTerms resumed imported roots)
        pure (compacted, raw, terms, Bridge.bindingCount nextBindings,
          trail, oldInterns, newInterns, invalidated, oldTerms, frozenTerms)
  case result of
    (compacted, raw, terms, count, trail, oldInterns, newInterns, invalidated, oldTerms, frozenTerms) -> do
      sameMetadata compacted initial
      stSubst (Reference.ssStore compacted) === expectedSubst
      raw === syntax
      terms === expectedTerms
      last terms === Var (fixtureFree sample)
      count === IS.size liveIds
      trail === 0
      assert (fst newInterns < fst oldInterns)
      assert (and invalidated)
      oldTerms === expectedTerms
      frozenTerms === expectedTerms

prop_generated_accepted_state_does_not_resurrect_fresh_range :: Property
prop_generated_accepted_state_does_not_resurrect_fresh_range = withTests 200 . property $ do
  first <- forAll (Gen.int (Range.linear 1 5000))
  gap <- forAll (Gen.int (Range.linear 1 5000))
  bound <- forAll (Gen.integral (Range.linear (-1000) 1000))
  reverseAlias <- forAll Gen.bool
  let second = first + gap
      (alias, free) = if reverseAlias then (first, second) else (second, first)
      original = (Reference.initialState 0)
        {Reference.ssFresh = 1000000, Reference.ssStore = emptyStore
          {stSubst = IM.fromList [(alias, Var free), (second + 10000, Atom "dead")]}}
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [alias, free, second + 10000])
        synchronized <- must (Bridge.syncState heap bindings original {Reference.ssFresh = 0})
        (imported, roots) <- must (Bridge.importTerms heap synchronized [Var alias])
        (nextHeap, compactBindings, compacted, nextRoots) <- must
          (Bridge.rebuild heap imported [alias] original roots)
        let incoming = compacted {Reference.ssStore = (Reference.ssStore compacted)
              {stSubst = IM.insert free (IntLit bound) (stSubst (Reference.ssStore compacted))}}
        accepted <- must (Bridge.syncAcceptedState nextHeap compactBindings compacted incoming)
        terms <- must (Bridge.exportTerms nextHeap accepted nextRoots)
        size <- Heap.heapSize nextHeap
        pure (Bridge.bindingCount compactBindings, Bridge.bindingCount accepted,
          Reference.ssFresh compacted, terms, size)
  case result of
    (before, after, fresh, terms, size) -> do
      before === 2
      after === before
      fresh === 1000000
      terms === [IntLit bound]
      assert (size < 20)

prop_generated_frozen_branches_survive_rebuild :: Property
prop_generated_frozen_branches_survive_rebuild = withTests 100 . property $ do
  free <- forAll (Gen.int (Range.linear 1 9000))
  left <- forAll (Gen.integral (Range.linear (-100) 100))
  right <- forAll (Gen.integral (Range.linear (-100) 100))
  let original = Reference.initialState 0
      raw = Compound "box" [Var free, Var free]
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [free])
        (imported, roots) <- must (Bridge.importTerms heap bindings [raw])
        frozen <- Heap.freezeHeap heap
        (nextHeap, nextBindings, _, nextRoots) <- must
          (Bridge.rebuild heap imported [free] original roots)
        let branch value = do
              resumed <- Heap.thawHeap frozen
              (branchBindings, addresses) <- must
                (Bridge.importTerms resumed imported [Var free, IntLit value])
              case addresses of
                [variable, scalar] -> do
                  accepted <- must (Heap.unify resumed variable scalar)
                  if not accepted then error "free variable failed to bind" else pure ()
                  single <$> must (Bridge.exportTerms resumed branchBindings roots)
                _ -> error "bridge changed root count"
        first <- branch left
        second <- branch right
        repeated <- branch left
        unchanged <- single <$> must (Bridge.exportTerms nextHeap nextBindings nextRoots)
        parent <- single <$> must (Bridge.exportTerms heap imported roots)
        pure (first, second, repeated, unchanged, parent)
  case result of
    (first, second, repeated, unchanged, parent) -> do
      first === Compound "box" [IntLit left, IntLit left]
      second === Compound "box" [IntLit right, IntLit right]
      repeated === first
      unchanged === raw
      parent === raw

machineReclaimGroup :: Group
machineReclaimGroup = Group "machine reclamation"
  [ ("generated_raw_roots_and_complete_metadata", prop_generated_raw_roots_and_complete_metadata),
    ("generated_accepted_state_does_not_resurrect_fresh_range", prop_generated_accepted_state_does_not_resurrect_fresh_range),
    ("generated_frozen_branches_survive_rebuild", prop_generated_frozen_branches_survive_rebuild)
  ]
