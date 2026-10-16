{-# LANGUAGE OverloadedStrings #-}

-- Normalization must change raw syntax exactly as the term evaluator does,
-- while retaining graph sharing and immutable branch ownership.
module MachineNormalizeTest (machineNormalizeGroup) where

import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IM
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.Arith (normArithTerm)
import Infera.CLP (emptyStore, stSubst)
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Bridge as Bridge
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

single :: [a] -> a
single [value] = value
single _ = error "expected exactly one root"

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["nil", "bad", "leaf"],
    IntLit <$> Gen.integral (Range.linear (-4) 4),
    FloatLit <$> Gen.element [-1 / 0, -2.5, -0.0, 0, 1.5, 1 / 0, 0 / 0],
    CharLit <$> Gen.element ['a', '\955'],
    StrLit <$> Gen.element ["", "kept", "\955"]
  ]

genTerm :: Int -> Gen Term
genTerm depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency
      [ (4, leaf),
        (3, Compound <$> Gen.element ["box", "pair", "cons", ";", "->", "$cut", "call"]
          <*> Gen.list (Range.linear 0 3) (genTerm (depth - 1))),
        (3, Compound <$> Gen.element ["plus", "minus", "mul", "div", "mod", "neg", "abs", "min", "max"]
          <*> Gen.list (Range.linear 0 3) (genTerm (depth - 1))),
        (1, Compound "^" <$> sequence
          [genTerm (depth - 1), IntLit <$> Gen.integral (Range.linear (-1) 3)])
      ]
  where
    leaf = Gen.choice [Var <$> Gen.int (Range.linear 0 5), genScalar]

-- Full raw exports retain logical variable IDs rather than canonicalizing
-- them, so an incorrect alias representative cannot hide in this comparison.
prop_generated_raw_normalization_parity :: Property
prop_generated_raw_normalization_parity = withTests 400 . property $ do
  source <- forAll (genTerm 3)
  assignments <- forAll . Gen.list (Range.linear 0 8) $
    (,) <$> (Var <$> Gen.int (Range.linear 0 5)) <*> genTerm 1
  let substitution = foldl accept Unify.emptySubst assignments
      accept current (left, right) = maybe current id (Unify.unifyPlain current left right)
      expected = normArithTerm substitution source
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0 .. 5])
        let state = (Reference.initialState 6) {Reference.ssStore = emptyStore {stSubst = substitution}}
        synchronized <- must (Bridge.syncState heap bindings state)
        (ready, roots) <- must (Bridge.importTerms heap synchronized [source])
        let original = single roots
        before <- must (Bridge.exportRawTerms heap ready [original])
        normalized <- must (Bridge.normalizeTermGraph heap ready original)
        raw <- must (Bridge.exportRawTerms heap ready [normalized])
        size <- Heap.heapSize heap
        repeated <- must (Bridge.normalizeTermGraph heap ready normalized)
        repeatedSize <- Heap.heapSize heap
        after <- must (Bridge.exportRawTerms heap ready [original])
        pure (map observe raw, map observe before, map observe after,
          normalized == repeated, size, repeatedSize)
  case result of
    (actual, before, after, sameAddress, size, repeatedSize) -> do
      actual === [observe expected]
      before === [observe source]
      after === before
      assert sameAddress
      repeatedSize === size

prop_shared_alias_suffix_is_normalized_once :: Property
prop_shared_alias_suffix_is_normalized_once = unit $ do
  let count = 512
      source = mkList (replicate count (Var 0)) Nothing
      expected = Compound "pair" (replicate 2 (mkList (replicate count (Var 1)) Nothing))
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0, 1])
        -- Accepted callers can direct a smaller logical ID at a larger one.
        let state = (Reference.initialState 2) {Reference.ssStore = emptyStore
              {stSubst = IM.singleton 0 (Var 1)}}
        synchronized <- must (Bridge.syncState heap bindings state)
        (ready, roots) <- must (Bridge.importTerms heap synchronized [source])
        let suffix = single roots
        original <- must (Heap.newCompound heap "pair" [suffix, suffix])
        beforeSize <- Heap.heapSize heap
        normalized <- must (Bridge.normalizeTermGraph heap ready original)
        afterSize <- Heap.heapSize heap
        raw <- must (Bridge.exportRawTerms heap ready [normalized])
        shape <- must (Heap.viewRaw heap normalized)
        pure (map observe raw, afterSize - beforeSize,
          case shape of Heap.CompoundView "pair" [left, right] -> left == right; _ -> False)
  case result of
    (actual, allocated, shared) -> do
      actual === [observe expected]
      allocated === count + 1
      assert shared

prop_unchanged_graph_and_nan_bits_are_reused :: Property
prop_unchanged_graph_and_nan_bits_are_reused = unit $ do
  let nan = 0 / 0
      source = Compound "box" [FloatLit nan, FloatLit (-0.0), mkList (replicate 256 (IntLit 7)) Nothing]
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [])
        (ready, roots) <- must (Bridge.importTerms heap bindings [source])
        let original = single roots
        size <- Heap.heapSize heap
        normalized <- must (Bridge.normalizeTermGraph heap ready original)
        finalSize <- Heap.heapSize heap
        raw <- must (Bridge.exportRawTerms heap ready [normalized])
        pure (original == normalized, size == finalSize, map observe raw)
  case result of
    (sameAddress, sameSize, raw) -> do
      assert sameAddress
      assert sameSize
      raw === [observe source]

prop_arithmetic_errors_and_partial_values_stay_symbolic :: Property
prop_arithmetic_errors_and_partial_values_stay_symbolic = unit $ do
  let huge = 2 ^ (100 :: Int)
      source = Compound "cases"
        [ Compound "div" [IntLit 1, IntLit 0],
          Compound "plus" [Var 0, Compound "mul" [IntLit 2, IntLit 3]],
          Compound "^" [IntLit 2, IntLit (-1)],
          Compound "mod" [IntLit 3, FloatLit 1.5],
          Compound "plus" [Atom "bad", Compound "abs" [IntLit (-7)]],
          Compound "plus" [IntLit huge, IntLit huge],
          Compound "plus" [],
          Compound "mul" [FloatLit (0 / 0), FloatLit 2]
        ]
      actual = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0])
        (ready, roots) <- must (Bridge.importTerms heap bindings [source])
        normalized <- must (Bridge.normalizeTermGraph heap ready (single roots))
        map observe <$> must (Bridge.exportRawTerms heap ready [normalized])
  actual === [observe (normArithTerm Unify.emptySubst source)]

prop_normalization_rollbacks_and_frozen_branches_are_independent :: Property
prop_normalization_rollbacks_and_frozen_branches_are_independent = unit $ do
  let source = Compound "box" [Compound "plus" [IntLit 2, IntLit 3], Var 0]
      result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0])
        (ready, roots) <- must (Bridge.importTerms heap bindings [source])
        let original = single roots
        mark <- Heap.checkpoint heap
        beforeSizes <- (,) <$> Heap.heapSize heap <*> Heap.trailSize heap
        before <- Heap.freezeHeap heap
        normalized <- must (Bridge.normalizeTermGraph heap ready original)
        retained <- Heap.freezeHeap heap
        first <- must (Bridge.exportRawTerms heap ready [normalized])
        _ <- must (Heap.rollback heap mark)
        afterSizes <- (,) <$> Heap.heapSize heap <*> Heap.trailSize heap
        invalid <- Heap.viewRaw heap normalized
        repeated <- must (Bridge.normalizeTermGraph heap ready original)
        repeatedTerms <- must (Bridge.exportRawTerms heap ready [repeated])
        old <- Heap.thawHeap before
        fromOld <- must (Bridge.normalizeTermGraph old ready original)
        oldTerms <- must (Bridge.exportRawTerms old ready [fromOld])
        saved <- Heap.thawHeap retained
        savedTerms <- must (Bridge.exportRawTerms saved ready [normalized])
        pure (map observe first, map observe repeatedTerms, map observe oldTerms, map observe savedTerms,
          beforeSizes, afterSizes, case invalid of Left (Heap.InvalidAddress _) -> True; _ -> False)
  case result of
    (first, repeated, old, saved, beforeSizes, afterSizes, stale) -> do
      first === [observe (normArithTerm Unify.emptySubst source)]
      repeated === first
      old === first
      saved === first
      afterSizes === beforeSizes
      assert stale

prop_failed_normalization_and_stale_constructor_are_atomic :: Property
prop_failed_normalization_and_stale_constructor_are_atomic = unit $ do
  let result = runST $ do
        heap <- Heap.newHeap
        bindings <- must (Bridge.newBindings heap [0])
        (ready, roots) <- must (Bridge.importTerms heap bindings
          [Compound "plus" [IntLit 1, IntLit 2], Var 0])
        case roots of
          [arithmetic, variable] -> do
            unnamed <- must (Heap.newVariable heap)
            malformed <- must (Heap.newCompound heap "pair" [arithmetic, unnamed])
            before <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
            rejected <- Bridge.normalizeTermGraph heap ready malformed
            after <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
            mark <- Heap.checkpoint heap
            doomed <- must (Heap.importTerm heap (Atom "discarded"))
            _ <- must (Heap.rollback heap mark)
            constructor <- Heap.newCompound heap "invalid_child" [variable, doomed]
            afterConstructor <- (,,) <$> Heap.heapSize heap <*> Heap.trailSize heap <*> Heap.internSize heap
            occurs <- must (Heap.newCompound heap "self" [variable])
            cyclic <- must (Heap.unify heap variable occurs)
            pure (case rejected of Left Heap.IncompatibleBindings -> True; _ -> False,
              case constructor of Left (Heap.InvalidAddress _) -> True; _ -> False,
              before, after, afterConstructor, cyclic)
          _ -> error "import changed the number of roots"
  case result of
    (rejected, stale, before, after, afterConstructor, cyclic) -> do
      assert rejected
      assert stale
      after === before
      afterConstructor === before
      assert (not cyclic)

machineNormalizeGroup :: Group
machineNormalizeGroup = Group "machine normalization"
  [ ("generated_raw_normalization_parity", prop_generated_raw_normalization_parity),
    ("shared_alias_suffix_is_normalized_once", prop_shared_alias_suffix_is_normalized_once),
    ("unchanged_graph_and_nan_bits_are_reused", prop_unchanged_graph_and_nan_bits_are_reused),
    ("arithmetic_errors_and_partial_values_stay_symbolic", prop_arithmetic_errors_and_partial_values_stay_symbolic),
    ("normalization_rollbacks_and_frozen_branches_are_independent", prop_normalization_rollbacks_and_frozen_branches_are_independent),
    ("failed_normalization_and_stale_constructor_are_atomic", prop_failed_normalization_and_stale_constructor_are_atomic)
  ]
