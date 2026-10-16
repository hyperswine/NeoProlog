-- | Flat first-order clause activation. Compiled operands refer to local
-- registers and logical variable offsets; activation never renames or walks
-- the source head/body terms. Control, lookup, unification and backtracking
-- remain owned by the native driver in this first bytecode milestone.
module Infera.Machine.Bytecode (instantiate) where

import Control.Monad (forM_, unless, when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.ST (ST)
import Control.Monad.Trans.Class (lift)
import Data.Array (Array, (!), listArray)
import Data.Array.MArray (newArray, readArray, writeArray)
import Data.Array.ST (STArray)
import Infera.Compile
import qualified Infera.Machine.Bridge as Bridge
import Infera.Machine.Heap (Address, Heap, HeapError (..))
import qualified Infera.Machine.Heap as Heap
import Infera.Syntax (Term (..), VarId)

type ActivationM s = ExceptT HeapError (ST s)

checked :: ST s (Either HeapError a) -> ActivationM s a
checked action = lift action >>= either throwError pure

newSlots :: Int -> ST s (STArray s Int (Maybe Address))
newSlots count = newArray (0, count - 1) Nothing

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
