{-# LANGUAGE OverloadedStrings #-}

-- The compiler/VM boundary has an independent interpreted activation oracle.
-- Raw exports retain logical IDs and floating bits; snapshots retain the
-- exact bindings whose addresses belong to each frozen heap.
module MachineBytecodeHeapTest (machineBytecodeHeapGroup) where

import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP (emptyStore, stSubst)
import Infera.Compile (compileClause)
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.Bytecode as Bytecode
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

must :: Show err => ST s (Either err a) -> ST s a
must action = action >>= either (error . show) pure

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["nil", "leaf", "true", "\955"],
    IntLit <$> Gen.choice
      [Gen.integral (Range.linear (-7) 7), pure (2 ^ (90 :: Int) + 3)],
    FloatLit <$> Gen.element
      [-1 / 0, -2.5, -0.0, 0.0, 1.5, 1 / 0, castWord64ToDouble 0x7ff8000000000042],
    CharLit <$> Gen.element ['a', '\955', '\0'],
    StrLit <$> Gen.element ["", "kept", "\955", "\0"]
  ]

genTerm :: Int -> Int -> Gen Term
genTerm count depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency
      [ (4, leaf),
        (3, Compound <$> Gen.element ["node", "pair", "cons", "plus", ";", "->", "call"]
          <*> Gen.list (Range.linear 0 3) (genTerm count (depth - 1)))
      ]
  where
    leaf
      | count <= 0 = genScalar
      | otherwise = Gen.frequency
          [(3, genScalar), (2, Var <$> Gen.int (Range.linear 0 (count - 1)))]

genClause :: Gen Clause
genClause = do
  count <- Gen.int (Range.linear 0 6)
  headTerm <- Gen.choice
    [ pure (Atom "p"),
      Compound "p" <$> Gen.list (Range.linear 0 4) (genTerm count 2)
    ]
  body <- Gen.list (Range.linear 0 5) $ Compound
    <$> Gen.element ["q", "unify", "is", "gt", "str_length", "range"]
    <*> Gen.list (Range.linear 0 3) (genTerm count 2)
  pure (Clause headTerm body count)

prop_generated_activation_matches_interpreted_import :: Property
prop_generated_activation_matches_interpreted_import = withTests 400 . property $ do
  clause <- forAll genClause
  base <- forAll (Gen.int (Range.linear 3 1000))
  overlap <- forAll Gen.bool
  code <- evalMaybe (compileClause clause)
  let count = max 1 (clauseNVars clause)
      previousSubst = if overlap then IM.singleton base (Var 0) else IM.empty
      expected = Unify.renameTerm base (clauseHead clause)
        : map (Unify.renameBody base) (clauseBody clause)
      expectedValues = map (Unify.deepWalk previousSubst) expected
      result = runST $ do
        original <- Heap.newHeap
        bindings <- must (Bridge.newBindings original [0, base + count + 100])
        let state = (Reference.initialState 0)
              {Reference.ssStore = emptyStore {stSubst = previousSubst}}
        ready <- must (Bridge.syncState original bindings state)
        frozen <- Heap.freezeHeap original
        compiled <- Heap.thawHeap frozen
        (compiledBindings, headAddress, bodyAddresses) <- must
          (Bytecode.instantiate compiled ready base code)
        raw <- must (Bridge.exportRawTerms compiled compiledBindings (headAddress : bodyAddresses))
        values <- must (Bridge.exportTerms compiled compiledBindings (headAddress : bodyAddresses))
        interpreted <- Heap.thawHeap frozen
        (interpretedBindings, addresses) <- must (Bridge.importTerms interpreted ready
          (map Var [base .. base + count - 1] ++ expected))
        let interpretedRoots = drop count addresses
        interpretedRaw <- must (Bridge.exportRawTerms interpreted interpretedBindings interpretedRoots)
        interpretedValues <- must (Bridge.exportTerms interpreted interpretedBindings interpretedRoots)
        pure (map observe raw, map observe values, map observe interpretedRaw, map observe interpretedValues,
          Bridge.bindingVariables compiledBindings, Bridge.bindingVariables interpretedBindings)
  case result of
    (raw, values, interpretedRaw, interpretedValues, compiledVariables, interpretedVariables) -> do
      raw === map observe expected
      raw === interpretedRaw
      values === map observe expectedValues
      values === interpretedValues
      compiledVariables === interpretedVariables

prop_repeated_variables_share_head_and_body_roots :: Property
prop_repeated_variables_share_head_and_body_roots = unit $ do
  code <- evalMaybe (compileClause (Clause
    (Compound "p" [Compound "pair" [Var 0, Var 0], Var 1])
    [Compound "q" [Var 0, Var 1], Compound "unify" [Var 1, Compound "box" [Var 0]]] 2))
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [])
        (ready, headAddress, bodyAddresses) <- must (Bytecode.instantiate heap bindings 30 code)
        headShape <- must (Heap.viewRaw heap headAddress)
        case (headShape, bodyAddresses) of
          (Heap.CompoundView "p" [pair, y], [q, equality]) -> do
            pairShape <- must (Heap.viewRaw heap pair)
            qShape <- must (Heap.viewRaw heap q)
            equalityShape <- must (Heap.viewRaw heap equality)
            let sharing = case (pairShape, qShape, equalityShape) of
                  (Heap.CompoundView "pair" [x, repeated], Heap.CompoundView "q" [bodyX, bodyY],
                    Heap.CompoundView "unify" [boundY, _]) -> x == repeated && x == bodyX && y == bodyY && y == boundY
                  _ -> False
            raw <- must (Bridge.exportRawTerms heap ready (headAddress : bodyAddresses))
            pure (sharing, raw, Bridge.bindingVariables ready)
          _ -> error "compiled activation changed constructor shape"
  case result of
    (sharing, raw, variables) -> do
      assert sharing
      variables === [30, 31]
      raw === [Compound "p" [Compound "pair" [Var 30, Var 30], Var 31],
        Compound "q" [Var 30, Var 31], Compound "unify" [Var 31, Compound "box" [Var 30]]]

prop_ground_clause_reserves_owner_and_keeps_scalar_bits :: Property
prop_ground_clause_reserves_owner_and_keeps_scalar_bits = unit $ do
  let source = Compound "p" [Atom "same", Compound "same" [],
        FloatLit (castWord64ToDouble 0x7ff8000000000042), FloatLit (-0.0), FloatLit 0.0]
  code <- evalMaybe (compileClause (Clause source [] 0))
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [])
        (ready, headAddress, bodyAddresses) <- must (Bytecode.instantiate heap bindings 80 code)
        raw <- must (Bridge.exportRawTerms heap ready [headAddress])
        pure (map observe raw, null bodyAddresses, Bridge.bindingVariables ready)
  case result of
    (raw, noBody, variables) -> do
      raw === [observe source]
      assert noBody
      variables === [80]

prop_compiled_occurs_checks_and_nan_unification_remain_exact :: Property
prop_compiled_occurs_checks_and_nan_unification_remain_exact = unit $ do
  let nan = castWord64ToDouble 0x7ff8000000000042
  code <- evalMaybe (compileClause (Clause
    (Compound "p" [Var 0, Compound "self" [Var 0], Compound "ground" [FloatLit nan]]) [] 1))
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [])
        (ready, headAddress, _) <- must (Bytecode.instantiate heap bindings 10 code)
        shape <- must (Heap.viewRaw heap headAddress)
        case shape of
          Heap.CompoundView "p" [variable, recursive, withNaN] -> do
            before <- (,) <$> Heap.heapSize heap <*> Heap.trailSize heap
            cycleAccepted <- must (Heap.unify heap variable recursive)
            after <- (,) <$> Heap.heapSize heap <*> Heap.trailSize heap
            directNaN <- must (Heap.unify heap withNaN withNaN)
            mark <- Heap.checkpoint heap
            bound <- must (Heap.unify heap variable withNaN)
            boundSelf <- must (Heap.unify heap variable variable)
            value <- must (Bridge.exportTerms heap ready [variable])
            _ <- must (Heap.rollback heap mark)
            restored <- must (Bridge.exportTerms heap ready [variable])
            pure (cycleAccepted, directNaN, bound, boundSelf, before, after, map observe value, restored)
          _ -> error "compiled activation changed constructor shape"
  case result of
    (cycleAccepted, directNaN, bound, boundSelf, before, after, value, restored) -> do
      assert (not cycleAccepted)
      assert (not directNaN)
      assert bound
      assert (not boundSelf)
      after === before
      value === [observe (Compound "ground" [FloatLit nan])]
      restored === [Var 10]

prop_stale_environment_rejection_and_overflow_are_atomic :: Property
prop_stale_environment_rejection_and_overflow_are_atomic = unit $ do
  ground <- evalMaybe (compileClause (Clause (Compound "p" [IntLit 1]) [] 0))
  twoVariables <- evalMaybe (compileClause (Clause (Compound "p" [Var 0, Var 1]) [] 2))
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0])
        mark <- Heap.checkpoint heap
        (future, _) <- must (Bridge.importTerms heap bindings [Var 100])
        _ <- must (Heap.rollback heap mark)
        before <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        -- Local 0 already exists; validation must still reject the stale
        -- historical frontier rather than inspecting only requested locals.
        stale <- Bytecode.instantiate heap future 0 ground
        afterStale <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        overflowOne <- Bytecode.instantiate heap bindings maxBound ground
        overflowTwo <- Bytecode.instantiate heap bindings (maxBound - 1) twoVariables
        afterOverflow <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
        (ready, headAddress, _) <- must (Bytecode.instantiate heap bindings (maxBound - 2) twoVariables)
        raw <- must (Bridge.exportRawTerms heap ready [headAddress])
        pure (case stale of Left (Heap.InvalidAddress _) -> True; _ -> False,
          case overflowOne of Left Heap.HeapCapacityExceeded -> True; _ -> False,
          case overflowTwo of Left Heap.HeapCapacityExceeded -> True; _ -> False,
          before, afterStale, afterOverflow, raw)
  case result of
    (stale, overflowOne, overflowTwo, before, afterStale, afterOverflow, raw) -> do
      assert stale
      assert overflowOne
      assert overflowTwo
      afterStale === before
      afterOverflow === before
      raw === [Compound "p" [Var (maxBound - 2), Var (maxBound - 1)]]

prop_interleaved_frozen_activations_keep_their_own_roots :: Property
prop_interleaved_frozen_activations_keep_their_own_roots = unit $ do
  code <- evalMaybe (compileClause (Clause (Compound "p" [Var 0, Var 1]) [Compound "q" [Var 0]] 2))
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [])
        (firstBindings, firstHead, _) <- must (Bytecode.instantiate heap bindings 10 code)
        firstFrozen <- Heap.freezeHeap heap
        (bothBindings, secondHead, _) <- must (Bytecode.instantiate heap firstBindings 20 code)
        bothFrozen <- Heap.freezeHeap heap
        firstShape <- must (Heap.viewRaw heap firstHead)
        secondShape <- must (Heap.viewRaw heap secondHead)
        case (firstShape, secondShape) of
          (Heap.CompoundView "p" [first, _], Heap.CompoundView "p" [second, _]) -> do
            one <- must (Heap.importTerm heap (IntLit 1))
            two <- must (Heap.importTerm heap (IntLit 2))
            _ <- must (Heap.unify heap first one)
            _ <- must (Heap.unify heap second two)
            live <- must (Bridge.exportTerms heap bothBindings [firstHead, secondHead])
            retainedFirst <- Heap.thawHeap firstFrozen
            firstOnly <- must (Bridge.exportTerms retainedFirst firstBindings [firstHead])
            retainedBoth <- Heap.thawHeap bothFrozen
            beforeOther <- must (Bridge.exportTerms retainedBoth bothBindings [firstHead, secondHead])
            three <- must (Heap.importTerm retainedBoth (IntLit 3))
            _ <- must (Heap.unify retainedBoth second three)
            afterOther <- must (Bridge.exportTerms retainedBoth bothBindings [firstHead, secondHead])
            repeatedBoth <- Heap.thawHeap bothFrozen
            repeated <- must (Bridge.exportTerms repeatedBoth bothBindings [firstHead, secondHead])
            Heap.restoreHeap heap firstFrozen
            staleBefore <- Heap.viewRaw heap secondHead
            (newBindings, newHead, _) <- must (Bytecode.instantiate heap firstBindings 20 code)
            staleAfter <- Heap.viewRaw heap secondHead
            reinstantiated <- must (Bridge.exportTerms heap newBindings [firstHead, newHead])
            let stale outcome = case outcome of Left (Heap.InvalidAddress _) -> True; _ -> False
            pure (live, firstOnly, beforeOther, afterOther, repeated, reinstantiated,
              stale staleBefore, stale staleAfter, newHead /= secondHead)
          _ -> error "compiled activation changed constructor shape"
  case result of
    (live, firstOnly, beforeOther, afterOther, repeated, reinstantiated, staleBefore, staleAfter, freshGeneration) -> do
      live === [Compound "p" [IntLit 1, Var 11], Compound "p" [IntLit 2, Var 21]]
      firstOnly === [Compound "p" [Var 10, Var 11]]
      beforeOther === [Compound "p" [Var 10, Var 11], Compound "p" [Var 20, Var 21]]
      afterOther === [Compound "p" [Var 10, Var 11], Compound "p" [IntLit 3, Var 21]]
      repeated === beforeOther
      reinstantiated === beforeOther
      assert staleBefore
      assert staleAfter
      assert freshGeneration

machineBytecodeHeapGroup :: Group
machineBytecodeHeapGroup = Group "machine bytecode activation heap"
  [ ("generated_activation_matches_interpreted_import", prop_generated_activation_matches_interpreted_import),
    ("repeated_variables_share_head_and_body_roots", prop_repeated_variables_share_head_and_body_roots),
    ("ground_clause_reserves_owner_and_keeps_scalar_bits", prop_ground_clause_reserves_owner_and_keeps_scalar_bits),
    ("compiled_occurs_checks_and_nan_unification_remain_exact", prop_compiled_occurs_checks_and_nan_unification_remain_exact),
    ("stale_environment_rejection_and_overflow_are_atomic", prop_stale_environment_rejection_and_overflow_are_atomic),
    ("interleaved_frozen_activations_keep_their_own_roots", prop_interleaved_frozen_activations_keep_their_own_roots)
  ]
