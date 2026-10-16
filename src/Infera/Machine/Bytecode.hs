{-# LANGUAGE BangPatterns #-}

-- | Flat first-order clause activation. Compiled operands refer to local
-- registers and logical variable offsets; activation never renames or walks
-- the source head/body terms. Control, lookup, unification and backtracking
-- remain owned by the native driver in this first bytecode milestone.
module Infera.Machine.Bytecode
  ( Activation (..),
    HeadActivation (..),
    BodyFrame,
    BodyStep (..),
    activate,
    activateMeasured,
    activateHead,
    activateHeadMeasured,
    materializeNext,
    materializeNextMeasured,
    frameVariables,
    instantiate,
  )
where

import Control.Monad (forM_, unless, when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.ST (ST)
import Control.Monad.Trans.Class (lift)
import Data.Array (Array, (!), listArray)
import Data.Array.MArray (newArray, readArray, writeArray)
import Data.Array.ST (STArray)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef, writeSTRef)
import Infera.CLP (Store)
import Infera.Compile
import Infera.Error (SolveError)
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.CLP as NativeCLP
import Infera.Machine.Heap (Address, Heap, HeapError (..))
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax (Term (..), VarId)

type ActivationM s = ExceptT HeapError (ST s)

checked :: ST s (Either HeapError a) -> ActivationM s a
checked action = lift action >>= either throwError pure

newSlots :: Int -> ST s (STArray s Int (Maybe Address))
newSlots count = newArray (0, count - 1) Nothing

-- | An accepted compiled activation. Instruction counts describe this
-- accepted activation only. Avoided cells count known compound head nodes,
-- and register slots count the lazily allocated temporary array, excluding
-- the stable logical-variable roots.
data Activation = Activation
  { activationBindings :: !Bridge.Bindings,
    activationStore :: !Store,
    activationBodyRoots :: [Address],
    activationHeadInstructions :: !Int,
    activationAllocationInstructions :: !Int,
    activationHeadCellsAvoided :: !Int,
    activationRegisterSlots :: !Int
  }

-- | This continuation contains code and logical IDs only. Mutable construction
-- arrays and heap handles never survive materialization or a public resume.
-- The suffix list/set is shared with the immutable clause code.
data BodyFrame = BodyFrame !VarId ![GoalCode]

data HeadActivation = HeadActivation
  { headBindings :: !Bridge.Bindings,
    headStore :: !Store,
    headBodyFrame :: !(Maybe BodyFrame),
    headInstructions :: !Int,
    headAllocationInstructions :: !Int,
    headCellsAvoided :: !Int,
    headRegisterSlots :: !Int
  }

data BodyStep = BodyStep
  { stepRoot :: !Address,
    stepCall :: !BodyCall,
    stepNextFrame :: !(Maybe BodyFrame),
    stepAllocationInstructions :: !Int,
    stepRegisterSlots :: !Int
  }

-- | All source-local occurrences in the remaining body are live, including
-- output-only variables and variables nested in data. Convert the persistent
-- suffix set only at a collection boundary; no source AST is walked.
frameVariables :: BodyFrame -> [VarId]
frameVariables (BodyFrame base goals) = case goals of
  [] -> []
  goal : _ -> map (+ base) (IS.toAscList (goalSuffixVariables goal))

bodyFrame :: VarId -> [GoalCode] -> Maybe BodyFrame
bodyFrame _ [] = Nothing
bodyFrame base goals = Just (BodyFrame base goals)

data Construction s = Construction
  { constructionHeap :: !(Heap s),
    constructionVariables :: Array Int Address,
    constructionVariableCount :: !Int,
    constructionCode :: !ClauseCode,
    constructionRegisterLimit :: !Int,
    constructionSlots :: !(STRef s (Maybe (STArray s Int (Maybe Address)))),
    constructionInstructions :: !(Maybe (STRef s Int))
  }

-- | Match the compiled head against the caller graph before constructing any
-- body term. Known head constructors are inspected directly. A free caller
-- target materializes just the corresponding source subtree and uses the
-- ordinary occurs-checked heap unifier. All head writes reach CLP together,
-- after the complete structural match; propagating each leaf separately
-- would change the ordering of delayed errors and later mismatches.
--
-- The eager compatibility wrapper also owns all body allocations. The native
-- driver uses activateHead/materializeNext to build only the reached goal.
activate :: Heap s -> Bridge.Bindings -> Store -> Address -> VarId -> ClauseCode
  -> ST s (Either HeapError (Either SolveError (Maybe Activation)))
activate = activateWithMetrics False

-- | As 'activate', collecting accepted-activation instruction and register
-- statistics. Ordinary activation allocates no counter references and returns
-- zero in every statistics field.
activateMeasured :: Heap s -> Bridge.Bindings -> Store -> Address -> VarId -> ClauseCode
  -> ST s (Either HeapError (Either SolveError (Maybe Activation)))
activateMeasured = activateWithMetrics True

activateWithMetrics :: Bool -> Heap s -> Bridge.Bindings -> Store -> Address -> VarId -> ClauseCode
  -> ST s (Either HeapError (Either SolveError (Maybe Activation)))
activateWithMetrics measured heap bindings store goal base code = do
  mark <- Heap.checkpoint heap
  result <- runExceptT $ do
    accepted <- checked (activateHeadWithMetrics measured heap bindings store goal base code)
    case accepted of
      Left problem -> pure (Left problem)
      Right Nothing -> pure (Right Nothing)
      Right (Just activation) -> do
        (bodies, allocations, registers) <- materializeAll measured heap
          (headBindings activation) (headBodyFrame activation)
        pure (Right (Just (Activation (headBindings activation) (headStore activation)
          bodies (headInstructions activation)
          (headAllocationInstructions activation + allocations)
          (headCellsAvoided activation) (max (headRegisterSlots activation) registers))))
  restoreRejected heap mark result

materializeAll :: Bool -> Heap s -> Bridge.Bindings -> Maybe BodyFrame
  -> ActivationM s ([Address], Int, Int)
materializeAll _ _ _ Nothing = pure ([], 0, 0)
materializeAll measured heap bindings (Just frame) = do
  next <- checked (materializeNextWithMetrics measured heap bindings frame)
  case next of
    Nothing -> pure ([], 0, 0)
    Just step -> do
      (remaining, allocations, registers) <- materializeAll measured heap bindings (stepNextFrame step)
      pure (stepRoot step : remaining, stepAllocationInstructions step + allocations,
        max (stepRegisterSlots step) registers)

-- | Match and propagate a whole head, reserving every local logical ID but
-- constructing no body term. The returned frame is immutable and must have
-- frameVariables included in the active collector's logical roots.
activateHead :: Heap s -> Bridge.Bindings -> Store -> Address -> VarId -> ClauseCode
  -> ST s (Either HeapError (Either SolveError (Maybe HeadActivation)))
activateHead = activateHeadWithMetrics False

activateHeadMeasured :: Heap s -> Bridge.Bindings -> Store -> Address -> VarId -> ClauseCode
  -> ST s (Either HeapError (Either SolveError (Maybe HeadActivation)))
activateHeadMeasured = activateHeadWithMetrics True

activateHeadWithMetrics :: Bool -> Heap s -> Bridge.Bindings -> Store -> Address -> VarId -> ClauseCode
  -> ST s (Either HeapError (Either SolveError (Maybe HeadActivation)))
activateHeadWithMetrics measured heap bindings store goal base code = do
  mark <- Heap.checkpoint heap
  result <- runExceptT $ do
    let variableCount = codeVariableCount code
        registerLimit = codeHead code + 1
    (allocated, roots) <- checked (Bridge.allocateActivation heap bindings base variableCount)
    slots <- lift (newSTRef Nothing)
    instructions <- lift (if measured then Just <$> newSTRef 0 else pure Nothing)
    matching <- lift (if measured then Just <$> newSTRef (0, 0) else pure Nothing)
    let construction = Construction heap (listArray (0, variableCount - 1) roots)
          variableCount code registerLimit slots instructions
        matcher = runExceptT $ do
          (accepted, written, matched, avoided) <- matchHead construction
            (Bridge.compareVariables allocated) (codeHeadInstructions code) [goal]
          lift (forM_ matching (\counter -> writeSTRef counter (matched, avoided)))
          pure (accepted, written)
    accepted <- checked (NativeCLP.unifyUsing heap allocated store matcher)
    case accepted of
      Left problem -> pure (Left problem)
      Right Nothing -> pure (Right Nothing)
      Right (Just (updated, propagated)) -> do
        (matched, avoided) <- lift (maybe (pure (0, 0)) readSTRef matching)
        allocationCount <- lift (maybe (pure 0) readSTRef instructions)
        registers <- lift (if measured then readSTRef slots else pure Nothing)
        pure (Right (Just (HeadActivation updated propagated (bodyFrame base (codeGoals code))
          matched allocationCount avoided (maybe 0 (const registerLimit) registers))))
  restoreRejected heap mark result

restoreRejected :: Heap s -> Heap.Checkpoint -> Either HeapError (Either SolveError (Maybe value))
  -> ST s (Either HeapError (Either SolveError (Maybe value)))
restoreRejected heap mark result =
  case result of
    Right (Right (Just _)) -> pure result
    _ -> do
      restored <- Heap.rollback heap mark
      pure $ case restored of
        Left rollbackError -> Left rollbackError
        Right () -> result

-- | Construct exactly one reached body goal. All variable lookups are strict
-- and nonallocating: a missing future local is a collector ownership error,
-- not permission to resurrect a retired activation range. No heap addresses
-- or mutable registers are installed in the next frame.
materializeNext :: Heap s -> Bridge.Bindings -> BodyFrame
  -> ST s (Either HeapError (Maybe BodyStep))
materializeNext = materializeNextWithMetrics False

materializeNextMeasured :: Heap s -> Bridge.Bindings -> BodyFrame
  -> ST s (Either HeapError (Maybe BodyStep))
materializeNextMeasured = materializeNextWithMetrics True

materializeNextWithMetrics :: Bool -> Heap s -> Bridge.Bindings -> BodyFrame
  -> ST s (Either HeapError (Maybe BodyStep))
materializeNextWithMetrics _ _ _ (BodyFrame _ []) = pure (Right Nothing)
materializeNextWithMetrics measured heap bindings (BodyFrame base (goal : remaining)) = do
  mark <- Heap.checkpoint heap
  result <- runExceptT $ do
    let localIds = IS.toAscList (goalVariables goal)
        count = goalRegisterCount goal
    addresses <- checked (Bridge.lookupVariables heap bindings (map (+ base) localIds))
    let locals = IM.fromDistinctAscList (zip localIds addresses)
    when (count < 0) (throwError IncompatibleBindings)
    slots <- lift (newSlots count)
    let operand (Local local) = maybe (throwError IncompatibleBindings) pure (IM.lookup local locals)
        operand (Temporary register) = readSlot slots count register
        executeGoal instruction = case instruction of
          GoalConstant destination scalar -> do
            case scalar of
              Var _ -> throwError IncompatibleBindings
              Compound _ _ -> throwError IncompatibleBindings
              _ -> pure ()
            address <- checked (Heap.importTerm heap scalar)
            overwriteSlot slots count destination address
          GoalCompound destination name children -> do
            -- A destination may recycle a child's final-use register. Capture
            -- every child address before the destination overwrites any slot.
            childrenAddresses <- mapM operand children
            address <- checked (Heap.newCompound heap name childrenAddresses)
            overwriteSlot slots count destination address
    mapM_ executeGoal (goalInstructions goal)
    root <- operand (goalRoot goal)
    pure (Just (BodyStep root (goalCall goal) (bodyFrame base remaining)
      (if measured then length (goalInstructions goal) else 0)
      (if measured then count else 0)))
  case result of
    Right _ -> pure result
    Left problem -> do
      restored <- Heap.rollback heap mark
      pure $ case restored of
        Left rollbackError -> Left rollbackError
        Right () -> Left problem

-- Construction registers cache source syntax only. A matching caller's
-- compound is never installed here: it may contain caller VarIds where the
-- body template requires its original local VarIds, visible in shallow errors.
constructSlot :: Construction s -> Slot -> ActivationM s Address
constructSlot construction slot = do
  let code = constructionCode construction
      count = constructionRegisterLimit construction
      heap = constructionHeap construction
  when (slot < 0 || slot >= count) (throwError IncompatibleBindings)
  existingSlots <- lift (readSTRef (constructionSlots construction))
  slots <- case existingSlots of
    Just allocated -> pure allocated
    Nothing -> do
      allocated <- lift (newSlots count)
      lift (writeSTRef (constructionSlots construction) (Just allocated))
      pure allocated
  previous <- lift (readArray slots slot)
  case previous of
    Just address -> pure address
    Nothing -> do
      instruction <- maybe (throwError IncompatibleBindings) pure (codeInstructionAt code slot)
      address <- case instruction of
        UseVariable destination local -> do
          unless (destination == slot) (throwError IncompatibleBindings)
          localRoot construction local
        PutConstant destination scalar -> do
          unless (destination == slot) (throwError IncompatibleBindings)
          case scalar of
            Var _ -> throwError IncompatibleBindings
            Compound _ _ -> throwError IncompatibleBindings
            _ -> checked (Heap.importTerm heap scalar)
        PutCompound destination name children -> do
          unless (destination == slot && all (\child -> child >= 0 && child < slot) children)
            (throwError IncompatibleBindings)
          addresses <- mapM (constructSlot construction) children
          checked (Heap.newCompound heap name addresses)
      lift $ do
        writeArray slots slot (Just address)
        forM_ (constructionInstructions construction) (\counter -> modifySTRef' counter (+ 1))
      pure address

localRoot :: Construction s -> Int -> ActivationM s Address
localRoot construction local = do
  when (local < 0 || local >= constructionVariableCount construction)
    (throwError IncompatibleBindings)
  pure (constructionVariables construction ! local)

matchHead :: Construction s -> (Address -> Address -> Ordering)
  -> [HeadInstruction] -> [Address] -> ActivationM s (Bool, [Address], Int, Int)
matchHead construction order = go 0 0 []
  where
    heap = constructionHeap construction
    measured = case constructionInstructions construction of
      Just _ -> True
      Nothing -> False
    go !matched !avoided written [] [] = pure (True, reverse written, matched, avoided)
    go !matched !avoided written (instruction : rest) (target : pending) = do
      let nextCount = if measured then matched + 1 else 0
          unifyTarget expected following = do
            -- NativeCLP.unifyUsing owns the complete head transaction, with
            -- activate's outer checkpoint also owning root/node allocations.
            -- A failed leaf stops matching and rolls back through those
            -- owners, so it needs no duplicate checkpoint of its own.
            (accepted, changed) <- checked
              (Heap.unifyWithChangesInTransaction order heap target expected)
            if accepted then go nextCount avoided (reverse changed ++ written) following pending
              else pure (False, [], nextCount, avoided)
      case instruction of
        HeadVariable local -> localRoot construction local >>= \root -> unifyTarget root rest
        HeadConstant slot scalar -> do
          shape <- checked (Heap.view heap target)
          case shape of
            Heap.VariableView _ -> constructSlot construction slot >>= \root -> unifyTarget root rest
            _ | matchesScalar scalar shape -> go nextCount avoided written rest pending
              | otherwise -> pure (False, [], nextCount, avoided)
        HeadCompound slot name arity width -> do
          when (arity < 0 || width <= 0) (throwError IncompatibleBindings)
          shape <- checked (Heap.view heap target)
          case shape of
            Heap.VariableView _ -> do
              root <- constructSlot construction slot
              unifyTarget root (drop (width - 1) rest)
            Heap.CompoundView found children
              | name == found && arity == length children ->
                  go nextCount (if measured then avoided + 1 else 0) written rest (children ++ pending)
            _ -> pure (False, [], nextCount, avoided)
    go _ _ _ _ _ = throwError IncompatibleBindings

-- Typed scalar comparisons deliberately use numeric Double equality:
-- NaNs fail even when the same input handle appears in multiple positions.
matchesScalar :: Term -> Heap.CellView -> Bool
matchesScalar (Atom expected) (Heap.AtomView actual) = expected == actual
matchesScalar (IntLit expected) (Heap.IntegerView actual) = expected == actual
matchesScalar (FloatLit expected) (Heap.FloatView actual) = expected == actual
matchesScalar (CharLit expected) (Heap.CharacterView actual) = expected == actual
matchesScalar (StrLit expected) (Heap.StringView actual) = expected == actual
matchesScalar _ _ = False

-- | Instantiate one already-compiled clause at the caller's fresh-ID base.
-- Local variables share their stable roots across every register occurrence;
-- constructors point directly at previously initialized child registers.
-- Scalars alone use ordinary term import. No mutable register array escapes.
--
-- The complete activation is atomic, including root allocation, interning,
-- constructor construction and register validation. Its returned bindings
-- belong to this heap branch and must be saved/restored with that heap.
instantiate :: Heap s -> Bridge.Bindings -> VarId -> ClauseCode
  -> ST s (Either HeapError (Bridge.Bindings, Address, [Address]))
instantiate heap bindings base code = do
  mark <- Heap.checkpoint heap
  result <- runExceptT $ do
    let variableCount = codeVariableCount code
        slotCount = codeSlotCount code
    when (slotCount <= 0) (throwError IncompatibleBindings)
    (allocated, roots) <- checked (Bridge.allocateActivation heap bindings base variableCount)
    let variables = listArray (0, variableCount - 1) roots
    slots <- lift (newSlots slotCount)
    forM_ (codeInstructions code) (execute heap variables variableCount slots slotCount)
    headAddress <- readSlot slots slotCount (codeHead code)
    bodyAddresses <- mapM (readSlot slots slotCount . bodySlot) (codeBody code)
    pure (allocated, headAddress, bodyAddresses)
  case result of
    Right value -> pure (Right value)
    Left err -> do
      restored <- Heap.rollback heap mark
      pure $ case restored of
        Left rollbackError -> Left rollbackError
        Right () -> Left err

readSlot :: STArray s Int (Maybe Address) -> Int -> Slot -> ActivationM s Address
readSlot slots count slot = do
  when (slot < 0 || slot >= count) (throwError IncompatibleBindings)
  value <- lift (readArray slots slot)
  maybe (throwError IncompatibleBindings) pure value

writeSlot :: STArray s Int (Maybe Address) -> Int -> Slot -> Address -> ActivationM s ()
writeSlot slots count slot address = do
  when (slot < 0 || slot >= count) (throwError IncompatibleBindings)
  existing <- lift (readArray slots slot)
  unless (case existing of Nothing -> True; Just _ -> False) (throwError IncompatibleBindings)
  lift (writeArray slots slot (Just address))

-- Physical goal registers intentionally recycle a dead child's slot.
overwriteSlot :: STArray s Int (Maybe Address) -> Int -> Slot -> Address -> ActivationM s ()
overwriteSlot slots count slot address = do
  when (slot < 0 || slot >= count) (throwError IncompatibleBindings)
  lift (writeArray slots slot (Just address))

execute :: Heap s -> Array Int Address -> Int -> STArray s Int (Maybe Address) -> Int
  -> Instruction -> ActivationM s ()
execute heap variables variableCount slots slotCount instruction = case instruction of
  UseVariable destination local -> do
    when (local < 0 || local >= variableCount) (throwError IncompatibleBindings)
    writeSlot slots slotCount destination (variables ! local)
  PutConstant destination scalar -> do
    case scalar of
      Var _ -> throwError IncompatibleBindings
      Compound _ _ -> throwError IncompatibleBindings
      _ -> pure ()
    address <- checked (Heap.importTerm heap scalar)
    writeSlot slots slotCount destination address
  PutCompound destination name children -> do
    addresses <- mapM (readSlot slots slotCount) children
    address <- checked (Heap.newCompound heap name addresses)
    writeSlot slots slotCount destination address
