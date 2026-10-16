-- | The abstract machine's isolated term heap. This module does not select a
-- new execution engine. Mutable pages belong to one 'ST' scope; a 'FrozenHeap'
-- contains only immutable arrays and can be resumed independently more than
-- once. A resumed heap copies a shared page on its first write and freezing
-- copies only pages written since the previous freeze.
--
-- 'Address', 'Environment' and 'Checkpoint' are branch-owned handles. They may
-- be retained alongside a matching frozen heap, but must not be transferred
-- between independent heaps or divergent resumed branches. Bounds and
-- allocation generations detect discarded allocations within a branch; they
-- are not globally unique heap identities. In particular, an unparameterized
-- 'Address' can escape 'runST', so the type alone does not enforce ownership.
--
-- Structures initially hold a list of child addresses. Keeping the layout
-- opaque permits packed functor/argument cells in a later bytecode milestone.
-- Every binding is trailed, including young variables: trail elision will need
-- a separate proof covering all live rollback scopes. There is no untrailed
-- path compression or rational-tree unification. Raw graph relocation lives
-- here; the Control module owns collection safe points and live control roots.
module Infera.Machine.Heap
  ( Heap,
    FrozenHeap,
    Address,
    Environment,
    Checkpoint,
    HeapError (..),
    CellView (..),
    newHeap,
    newHeapSuccessor,
    thawHeap,
    freezeHeap,
    restoreHeap,
    emptyEnvironment,
    validateEnvironment,
    environmentFromRoots,
    copyReachable,
    newVariable,
    newCompound,
    newCompoundInTransaction,
    importTerm,
    importScalarInTransaction,
    importWithEnvironment,
    exportTerm,
    exportTerms,
    dereference,
    view,
    viewRaw,
    referenceTarget,
    rerootVariable,
    unify,
    unifyWithChanges,
    unifyWithChangesInTransaction,
    checkpoint,
    rollback,
    heapSize,
    trailSize,
    internSize,
    forgetTrail,
  )
where

import Control.Monad (foldM, forM_, unless, when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.ST (ST)
import Data.Array (Array, (!))
import Data.Array.MArray (freeze, newArray, readArray, thaw, writeArray)
import Data.Array.ST (STArray)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.STRef (STRef, modifySTRef', newSTRef, readSTRef, writeSTRef)
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64)
import Infera.Syntax (Term (..), VarId)

-- A generation never rewinds on rollback. Reusing a heap slot consequently
-- cannot silently revive a handle to its previous allocation.
data Address = Address !Int !Integer
  deriving (Eq, Ord, Show)

data HeapError
  = InvalidAddress !Address
  | InvalidCheckpoint
  | HeapCapacityExceeded
  | IncompatibleBindings
  deriving (Eq, Show)

-- | A dereferenced cell without exposing mutable heap storage. Child handles
-- retain the same branch ownership rules as any other 'Address'.
data CellView
  = VariableView !Address
  | AtomView !String
  | IntegerView !Integer
  | FloatView !Double
  | CharacterView !Char
  | StringView !String
  | CompoundView !String [Address]
  deriving (Eq, Show)

-- The greatest allocated root certifies the whole environment's allocation
-- prefix. Heap cells are only appended or suffix-truncated, and a retained
-- cell keeps its generation across bindings and rerooting. Consequently, in
-- the same branch, an older root cannot become stale while this root survives.
-- Keeping this witness avoids rescanning every source variable on each import.
-- Divergent branches still obey the handle ownership contract above.
data Environment = Environment !(IntMap Address) !(Maybe Address)

emptyEnvironment :: Environment
emptyEnvironment = Environment IM.empty Nothing

-- | Validate an environment's allocation-prefix witness without importing,
-- allocating, dereferencing or opening a transaction. Under branch ownership,
-- the newest root certifies every earlier root, including entries that the
-- caller does not currently use. Even an empty requested-variable lookup must
-- validate this witness before accepting an existing environment.
validateEnvironment :: Heap s -> Environment -> ST s (Either HeapError ())
validateEnvironment heap (Environment _ frontier) =
  runExceptT $ forM_ frontier (readCell heap)

-- | Restore an activation environment from its existing raw variable roots.
-- Bound variables retain a raw reference cell and are accepted. Every entry
-- is validated before the constant-time allocation-prefix witness is made;
-- constants and structure handles cannot serve as source variable roots.
environmentFromRoots :: Heap s -> IntMap Address -> ST s (Either HeapError Environment)
environmentFromRoots heap roots = runExceptT $ do
  frontier <- foldM validate Nothing (IM.elems roots)
  pure (Environment roots frontier)
  where
    validate previous address = do
      cell <- readCell heap address
      case cell of
        Ref _ -> pure (Just (maybe address (max address) previous))
        _ -> throwError IncompatibleBindings

newtype ConstantId = ConstantId Int
  deriving (Eq)

newtype FunctorId = FunctorId Int
  deriving (Eq)

data Constant
  = AtomConstant !String
  | IntegerConstant !Integer
  | FloatConstant !Double
  | CharConstant !Char
  | StringConstant !String

-- Double's Ord is not a lawful map key in the presence of NaN. Bit keys are
-- used for interning only; unification compares the original Double values.
data ConstantKey
  = AtomKey !String
  | IntegerKey !Integer
  | FloatKey !Word64
  | CharKey !Char
  | StringKey !String
  deriving (Eq, Ord)

data Cell
  = Ref !Address
  | Con !ConstantId
  -- This flag means that the original constructor contains no variable
  -- occurrences, not that its currently dereferenced arguments are ground.
  -- Its immutable child graph cannot acquire a reference through a binding.
  | Structure !FunctorId !Bool [Address]

data Slot = Slot !Integer !Cell

data TrailEntry = TrailEntry !Integer !Address !Cell

data Interns = Interns
  { constantIds :: !(Map ConstantKey ConstantId),
    constants :: !(IntMap Constant),
    nextConstantId :: !Int,
    functorIds :: !(Map (String, Int) FunctorId),
    functors :: !(IntMap (String, Int)),
    nextFunctorId :: !Int
  }

emptyInterns :: Interns
emptyInterns = Interns Map.empty IM.empty 0 Map.empty IM.empty 0

-- Boxed, fixed-size pages also support exact Integers and scalar strings.
-- The arrays never expose mutable aliases. Nothing denotes an unused slot.
pageSize :: Int
pageSize = 256

data Page s a
  = Shared !(Array Int (Maybe a))
  | Writable !(STArray s Int (Maybe a))

data Paged s a = Paged
  { pages :: !(STRef s (IntMap (Page s a))),
    pagedTop :: !(STRef s Int)
  }

data FrozenPaged a = FrozenPaged !Int !(IntMap (Array Int (Maybe a)))

data Heap s = Heap
  { heapCells :: !(Paged s Slot),
    heapTrail :: !(Paged s TrailEntry),
    heapInterns :: !(STRef s Interns),
    nextSerial :: !(STRef s Integer)
  }

data FrozenHeap = FrozenHeap
  !(FrozenPaged Slot)
  !(FrozenPaged TrailEntry)
  !Interns
  !Integer

data Checkpoint = Checkpoint
  !Int                 -- heap top
  !Int                 -- trail top
  !(Maybe Integer)     -- generation at the retained heap frontier
  !(Maybe Integer)     -- serial at the retained trail frontier
  !Interns

type HeapM s = ExceptT HeapError (ST s)

newPaged :: ST s (Paged s a)
newPaged = Paged <$> newSTRef IM.empty <*> newSTRef 0

thawPaged :: FrozenPaged a -> ST s (Paged s a)
thawPaged (FrozenPaged top ps) =
  Paged <$> newSTRef (IM.map Shared ps) <*> newSTRef top

freezePaged :: Paged s a -> ST s (FrozenPaged a)
freezePaged buffer = do
  ps <- readSTRef (pages buffer)
  frozen <- traverse freezePage ps
  -- The next write also copies pages just frozen in this ST scope.
  writeSTRef (pages buffer) (IM.map Shared frozen)
  top <- readSTRef (pagedTop buffer)
  pure (FrozenPaged top frozen)

freezePage :: Page s a -> ST s (Array Int (Maybe a))
freezePage (Shared array) = pure array
freezePage (Writable array) = freeze array

writablePage :: Paged s a -> Int -> ST s (STArray s Int (Maybe a))
writablePage buffer page = do
  ps <- readSTRef (pages buffer)
  case IM.lookup page ps of
    Just (Writable array) -> pure array
    Just (Shared array) -> do
      mutable <- thaw array
      writeSTRef (pages buffer) (IM.insert page (Writable mutable) ps)
      pure mutable
    Nothing -> do
      mutable <- newArray (0, pageSize - 1) Nothing
      writeSTRef (pages buffer) (IM.insert page (Writable mutable) ps)
      pure mutable

peekPaged :: Paged s a -> Int -> ST s (Maybe a)
peekPaged buffer index = do
  top <- readSTRef (pagedTop buffer)
  if index < 0 || index >= top
    then pure Nothing
    else do
      ps <- readSTRef (pages buffer)
      let (page, offset) = index `quotRem` pageSize
      case IM.lookup page ps of
        Nothing -> pure Nothing
        Just (Shared array) -> pure (array ! offset)
        Just (Writable array) -> readArray array offset

writePaged :: Paged s a -> Int -> a -> ST s ()
writePaged buffer index value = do
  let (page, offset) = index `quotRem` pageSize
  array <- writablePage buffer page
  writeArray array offset (Just value)

appendPaged :: Paged s a -> a -> HeapM s ()
appendPaged buffer value = do
  top <- lift (readSTRef (pagedTop buffer))
  when (top == maxBound) (throwError HeapCapacityExceeded)
  lift $ do
    writePaged buffer top value
    writeSTRef (pagedTop buffer) (top + 1)

truncatePaged :: Paged s a -> Int -> ST s ()
truncatePaged buffer top = do
  oldTop <- readSTRef (pagedTop buffer)
  when (top < oldTop) $ do
    let (page, offset) = top `quotRem` pageSize
        lastPage = if offset == 0 then page - 1 else page
    modifySTRef' (pages buffer) (IM.filterWithKey (\key _ -> key <= lastPage))
    -- Drop dead references in the retained boundary page, too. In particular,
    -- freezing a short rollback must not retain a discarded argument vector.
    when (offset /= 0) $ do
      array <- writablePage buffer page
      forM_ [offset .. pageSize - 1] $ \index -> writeArray array index Nothing
    writeSTRef (pagedTop buffer) top

newHeap :: ST s (Heap s)
newHeap = Heap <$> newPaged <*> newPaged <*> newSTRef emptyInterns <*> newSTRef 1

-- | Start an empty replacement heap without recycling generations allocated
-- by its predecessor. A collector must stop using the old heap's handles and
-- checkpoints before installing this heap. Frozen snapshots remain independent
-- owners of the predecessor's immutable pages; this does not mutate them.
-- Generations still do not establish ownership across divergent resumptions.
newHeapSuccessor :: Heap s -> ST s (Heap s)
newHeapSuccessor previous = do
  serial <- readSTRef (nextSerial previous)
  Heap <$> newPaged <*> newPaged <*> newSTRef emptyInterns <*> newSTRef serial

-- | Copy precisely the raw graph reachable from these roots to a fresh
-- successor heap. Repeated addresses, shared constructor suffixes, reference
-- links and variable roots retain their identities under one relocation map.
-- No term export or dereferencing expands the graph into a tree.
--
-- Copied bindings form the new heap's baseline with an empty trail. The caller
-- must abandon active rollback checkpoints into the old heap; independently
-- frozen owners remain valid. The old heap is never mutated, including on
-- invalid input. Roots are returned in their supplied order, with duplicates.
copyReachable :: Heap s -> [Address] -> ST s (Either HeapError (Heap s, [Address]))
copyReachable previous roots = runExceptT $ do
  next <- lift (newHeapSuccessor previous)
  (relocation, copied) <- discover next Map.empty roots []
  forM_ copied $ \(Address index generation, cell) -> do
    relocated <- case cell of
      Ref target -> Ref <$> relocate relocation target
      Con ident -> do
        value <- lift (getConstant previous ident)
        ident' <- lift (internConstant next (constantKey value) value)
        pure (Con ident')
      Structure ident staticGround children -> do
        (name, arity) <- lift (getFunctor previous ident)
        ident' <- lift (internFunctor next name arity)
        children' <- mapM (relocate relocation) children
        pure (Structure ident' staticGround children')
    -- Destination cells are private until the whole graph has been copied.
    -- Initializing them directly creates no rollback history for the baseline.
    lift (writePaged (heapCells next) index (Slot generation relocated))
  relocatedRoots <- mapM (relocate relocation) roots
  pure (next, relocatedRoots)
  where
    discover _ relocation [] copied = pure (relocation, copied)
    discover next relocation (address : pending) copied
      | Map.member address relocation = discover next relocation pending copied
      | otherwise = do
          cell <- readCell previous address
          destination <- allocate next Ref
          let updated = Map.insert address destination relocation
              children = case cell of
                Ref target -> [target]
                Structure _ _ arguments -> arguments
                Con _ -> []
          updated `seq` discover next updated (children ++ pending)
            ((destination, cell) : copied)
    relocate :: Map Address Address -> Address -> HeapM s Address
    relocate relocation address = case Map.lookup address relocation of
      Just destination -> pure destination
      Nothing -> throwError (InvalidAddress address)

constantKey :: Constant -> ConstantKey
constantKey value = case value of
  AtomConstant scalar -> AtomKey scalar
  IntegerConstant scalar -> IntegerKey scalar
  FloatConstant scalar -> FloatKey (castDoubleToWord64 scalar)
  CharConstant scalar -> CharKey scalar
  StringConstant scalar -> StringKey scalar

thawHeap :: FrozenHeap -> ST s (Heap s)
thawHeap (FrozenHeap cells trail interns serial) =
  Heap <$> thawPaged cells <*> thawPaged trail <*> newSTRef interns <*> newSTRef serial

freezeHeap :: Heap s -> ST s FrozenHeap
freezeHeap heap =
  FrozenHeap <$> freezePaged (heapCells heap) <*> freezePaged (heapTrail heap)
    <*> readSTRef (heapInterns heap) <*> readSTRef (nextSerial heap)

-- | Install an immutable branch snapshot into an existing mutable heap.
-- Every page is shared until its first subsequent write, exactly as for
-- 'thawHeap'; no mutable array is retained by or aliases the snapshot. Cells,
-- trail, interning tables and frontiers are replaced together, so checkpoints
-- retained with this snapshot regain their original rollback lineage.
--
-- The caller must replace all active handles and checkpoints with the ones
-- owned by the installed snapshot. Handles into the displaced branch remain
-- valid only in a snapshot of that branch. Allocation serials never rewind:
-- a later allocation cannot revive a discarded handle after repeated restores.
-- As with 'thawHeap', independent snapshots do not establish global ownership.
restoreHeap :: Heap s -> FrozenHeap -> ST s ()
restoreHeap heap (FrozenHeap cells trail interns snapshotSerial) = do
  previousSerial <- readSTRef (nextSerial heap)
  restorePaged (heapCells heap) cells
  restorePaged (heapTrail heap) trail
  writeSTRef (heapInterns heap) interns
  writeSTRef (nextSerial heap) (max previousSerial snapshotSerial)

restorePaged :: Paged s a -> FrozenPaged a -> ST s ()
restorePaged buffer (FrozenPaged top saved) = do
  writeSTRef (pages buffer) (IM.map Shared saved)
  writeSTRef (pagedTop buffer) top

heapSize :: Heap s -> ST s Int
heapSize = readSTRef . pagedTop . heapCells

trailSize :: Heap s -> ST s Int
trailSize = readSTRef . pagedTop . heapTrail

internSize :: Heap s -> ST s (Int, Int)
internSize heap = do
  interns <- readSTRef (heapInterns heap)
  pure (IM.size (constants interns), IM.size (functors interns))

-- | Forget binding history when no surviving rollback checkpoint refers to
-- this heap. This operation leaves current cells untouched. In particular,
-- callers must not retain a checkpoint made before the history was dropped.
forgetTrail :: Heap s -> ST s ()
forgetTrail heap = truncatePaged (heapTrail heap) 0

freshSerial :: Heap s -> ST s Integer
freshSerial heap = do
  serial <- readSTRef (nextSerial heap)
  writeSTRef (nextSerial heap) (serial + 1)
  pure serial

allocate :: Heap s -> (Address -> Cell) -> HeapM s Address
allocate heap makeCell = do
  top <- lift (heapSize heap)
  when (top == maxBound) (throwError HeapCapacityExceeded)
  serial <- lift (freshSerial heap)
  let address = Address top serial
  appendPaged (heapCells heap) (Slot serial (makeCell address))
  pure address

newVariable :: Heap s -> ST s (Either HeapError Address)
newVariable heap = runExceptT (allocate heap Ref)

-- | Construct one immutable node from branch-owned child handles without
-- exporting or copying their graphs. Every child is validated before the
-- node becomes visible. The constructor cannot create a cycle because its
-- destination has not yet been allocated. Existing references remain dynamic
-- even when currently bound; rollback may expose their free variables again.
newCompound :: Heap s -> String -> [Address] -> ST s (Either HeapError Address)
newCompound heap name children = atomic heap (newCompoundAction heap name children)

-- | Trusted constructor allocation inside a transaction owned by the caller.
-- This validates every child and performs the same interning/allocation as
-- 'newCompound', but creates no nested checkpoint and does not roll back an
-- error. The caller must restore its checkpoint before exposing failure,
-- including any functor interned before a failed allocation. Use 'newCompound'
-- when that ownership proof is absent.
newCompoundInTransaction :: Heap s -> String -> [Address] -> ST s (Either HeapError Address)
newCompoundInTransaction heap name children = runExceptT (newCompoundAction heap name children)

newCompoundAction :: Heap s -> String -> [Address] -> HeapM s Address
newCompoundAction heap name children = do
  cells <- mapM (readCell heap) children
  let staticGround (Ref _) = False
      staticGround (Con _) = True
      staticGround (Structure _ ground _) = ground
  ident <- lift (internFunctor heap name (length children))
  allocate heap (const (Structure ident (all staticGround cells) children))

readCell :: Heap s -> Address -> HeapM s Cell
readCell heap address@(Address index generation) = do
  slot <- lift (peekPaged (heapCells heap) index)
  case slot of
    Just (Slot actual cell) | actual == generation -> pure cell
    _ -> throwError (InvalidAddress address)

writeCell :: Heap s -> Address -> Cell -> HeapM s ()
writeCell heap address@(Address index generation) cell = do
  old <- readCell heap address
  serial <- lift (freshSerial heap)
  appendPaged (heapTrail heap) (TrailEntry serial address old)
  lift (writePaged (heapCells heap) index (Slot generation cell))

deref :: Heap s -> Address -> HeapM s (Address, Cell)
deref heap address = do
  cell <- readCell heap address
  case cell of
    Ref target | target /= address -> deref heap target
    _ -> pure (address, cell)

dereference :: Heap s -> Address -> ST s (Either HeapError Address)
dereference heap address = runExceptT (fst <$> deref heap address)

view :: Heap s -> Address -> ST s (Either HeapError CellView)
view heap address = runExceptT $ do
  (target, cell) <- deref heap address
  viewCell heap target cell

-- | Inspect syntactic variable occurrences before dereferencing. A bound
-- variable remains a 'VariableView' of its original root, allowing callers
-- to preserve the reference interpreter's shallow control-pattern matches.
viewRaw :: Heap s -> Address -> ST s (Either HeapError CellView)
viewRaw heap address = runExceptT $ do
  cell <- readCell heap address
  viewCell heap address cell

-- | The direct target of a raw reference, including a free variable's self
-- reference. This retains binding syntax when exporting a substitution;
-- following all references would erase nested variable occurrences that the
-- reference evaluator deliberately inspects before deeper dereferencing.
referenceTarget :: Heap s -> Address -> ST s (Either HeapError (Maybe Address))
referenceTarget heap address = runExceptT $ do
  cell <- readCell heap address
  pure $ case cell of
    Ref target -> Just target
    _ -> Nothing

-- | Make a member of an existing free-variable class its representative.
-- Startup substitutions may intentionally point a lower logical ID at a
-- higher one. Reconciliation must preserve that identity rather than apply
-- the normal unifier's ordering to an already accepted substitution. Both
-- writes are trailed: breaking the desired member's link first prevents a
-- cycle, and linking the old root then redirects every class member.
rerootVariable :: Heap s -> Address -> ST s (Either HeapError ())
rerootVariable heap address = atomic heap $ do
  (root, cell) <- deref heap address
  case cell of
    Ref _
      | root == address -> pure ()
      | otherwise -> do
          writeCell heap address (Ref address)
          writeCell heap root (Ref address)
    _ -> throwError IncompatibleBindings

viewCell :: Heap s -> Address -> Cell -> HeapM s CellView
viewCell heap target cell =
  case cell of
    Ref _ -> pure (VariableView target)
    Con ident -> do
      value <- lift (getConstant heap ident)
      pure $ case value of
        AtomConstant scalar -> AtomView scalar
        IntegerConstant scalar -> IntegerView scalar
        FloatConstant scalar -> FloatView scalar
        CharConstant scalar -> CharacterView scalar
        StringConstant scalar -> StringView scalar
    Structure ident _ children -> do
      (name, _) <- lift (getFunctor heap ident)
      pure (CompoundView name children)

checkpoint :: Heap s -> ST s Checkpoint
checkpoint heap = do
  h <- heapSize heap
  tr <- trailSize heap
  hs <- peekPaged (heapCells heap) (h - 1)
  ts <- peekPaged (heapTrail heap) (tr - 1)
  interns <- readSTRef (heapInterns heap)
  pure (Checkpoint h tr (slotSerial <$> hs) (trailSerial <$> ts) interns)
  where
    slotSerial (Slot serial _) = serial
    trailSerial (TrailEntry serial _ _) = serial

rollback :: Heap s -> Checkpoint -> ST s (Either HeapError ())
rollback heap mark = runExceptT (rollbackTo heap mark)

rollbackTo :: Heap s -> Checkpoint -> HeapM s ()
rollbackTo heap (Checkpoint h tr hs ts interns) = do
  currentH <- lift (heapSize heap)
  currentTr <- lift (trailSize heap)
  when (h > currentH || tr > currentTr) (throwError InvalidCheckpoint)
  heapFrontier <- lift (peekPaged (heapCells heap) (h - 1))
  trailFrontier <- lift (peekPaged (heapTrail heap) (tr - 1))
  unless (fmap slotSerial heapFrontier == hs && fmap trailSerial trailFrontier == ts)
    (throwError InvalidCheckpoint)
  -- Restore writes while all their target allocations still exist. Only then
  -- may the heap top be rewound and branch-local allocations discarded.
  forM_ [currentTr - 1, currentTr - 2 .. tr] $ \index -> do
    entry <- lift (peekPaged (heapTrail heap) index)
    case entry of
      Nothing -> throwError InvalidCheckpoint
      Just (TrailEntry _ address@(Address target generation) old) -> do
        _ <- readCell heap address
        lift (writePaged (heapCells heap) target (Slot generation old))
  lift $ do
    truncatePaged (heapTrail heap) tr
    truncatePaged (heapCells heap) h
    writeSTRef (heapInterns heap) interns
  where
    slotSerial (Slot serial _) = serial
    trailSerial (TrailEntry serial _ _) = serial

-- Public operations that may fail are atomic even if failure follows several
-- successful bindings or allocations. The serial counter intentionally stays
-- monotonic, so a failed operation cannot revive discarded handles.
atomic :: Heap s -> HeapM s a -> ST s (Either HeapError a)
atomic heap action = do
  mark <- checkpoint heap
  result <- runExceptT action
  case result of
    Right value -> pure (Right value)
    Left err -> do
      restored <- rollback heap mark
      pure $ case restored of
        Left rollbackError -> Left rollbackError
        Right () -> Left err

internConstant :: Heap s -> ConstantKey -> Constant -> ST s ConstantId
internConstant heap key value = do
  interns <- readSTRef (heapInterns heap)
  case Map.lookup key (constantIds interns) of
    Just ident -> pure ident
    Nothing -> do
      let index = nextConstantId interns
          ident = ConstantId index
      writeSTRef (heapInterns heap) interns
        { constantIds = Map.insert key ident (constantIds interns),
          constants = IM.insert index value (constants interns),
          nextConstantId = index + 1
        }
      pure ident

internFunctor :: Heap s -> String -> Int -> ST s FunctorId
internFunctor heap name arity = do
  interns <- readSTRef (heapInterns heap)
  case Map.lookup (name, arity) (functorIds interns) of
    Just ident -> pure ident
    Nothing -> do
      let index = nextFunctorId interns
          ident = FunctorId index
      writeSTRef (heapInterns heap) interns
        { functorIds = Map.insert (name, arity) ident (functorIds interns),
          functors = IM.insert index (name, arity) (functors interns),
          nextFunctorId = index + 1
        }
      pure ident

-- | Instantiate one term with fresh variables. Repeated occurrences within
-- this term share an address; another call starts a distinct activation.
importTerm :: Heap s -> Term -> ST s (Either HeapError Address)
importTerm heap term = fmap (fmap fst) (importWithEnvironment heap emptyEnvironment term)

-- | Trusted scalar allocation inside a transaction owned by the caller.
-- Variables and compounds are rejected. Scalar interning preserves exact
-- floating-point bits, including signed zero and NaN payloads, as 'importTerm'
-- does. There is no nested checkpoint or rollback: a failed allocation may
-- leave an interned constant, which the enclosing transaction must restore
-- before exposing failure. Use 'importTerm' without that ownership proof.
importScalarInTransaction :: Heap s -> Term -> ST s (Either HeapError Address)
importScalarInTransaction heap scalar = runExceptT (importScalarAction heap scalar)

importScalarAction :: Heap s -> Term -> HeapM s Address
importScalarAction heap scalar = do
  (key, value) <- case scalar of
    Atom value -> pure (AtomKey value, AtomConstant value)
    IntLit value -> pure (IntegerKey value, IntegerConstant value)
    FloatLit value -> pure (FloatKey (castDoubleToWord64 value), FloatConstant value)
    CharLit value -> pure (CharKey value, CharConstant value)
    StrLit value -> pure (StringKey value, StringConstant value)
    Var _ -> throwError IncompatibleBindings
    Compound _ _ -> throwError IncompatibleBindings
  ident <- lift (internConstant heap key value)
  allocate heap (const (Con ident))

-- | Instantiate into an explicit activation environment. Share the returned
-- environment when importing a clause head and its body or several roots.
importWithEnvironment :: Heap s -> Environment -> Term -> ST s (Either HeapError (Address, Environment))
importWithEnvironment heap initial@(Environment _ frontier) term = atomic heap $ do
  -- Validate even unused entries, so a discarded environment cannot appear
  -- to work until one particular source variable happens to be encountered.
  -- Under branch ownership, the newest root validates every earlier root.
  forM_ frontier (readCell heap)
  (address, environment, _) <- importInto initial term
  pure (address, environment)
  where
    importInto environment@(Environment bindings _) (Var variable) = case IM.lookup variable bindings of
      -- A source variable remains dynamic even if it is bound right now:
      -- rollback can expose it again after this structure has been imported.
      Just address -> pure (address, environment, False)
      Nothing -> do
        address <- allocate heap Ref
        pure (address, Environment (IM.insert variable address bindings) (Just address), False)
    importInto environment (Compound name arguments) = do
      (addresses, final, staticGround) <- importArguments environment arguments
      ident <- lift (internFunctor heap name (length addresses))
      address <- allocate heap (const (Structure ident staticGround addresses))
      pure (address, final, staticGround)
    importInto environment scalar = do
      address <- importScalarAction heap scalar
      pure (address, environment, True)
    importArguments environment [] = pure ([], environment, True)
    importArguments environment (argument : rest) = do
      (address, next, staticArgument) <- importInto environment argument
      (addresses, final, staticRest) <- importArguments next rest
      pure (address : addresses, final, staticArgument && staticRest)

getConstant :: Heap s -> ConstantId -> ST s Constant
getConstant heap (ConstantId ident) = do
  interns <- readSTRef (heapInterns heap)
  case IM.lookup ident (constants interns) of
    Just value -> pure value
    Nothing -> error "Infera.Machine.Heap: missing interned constant"

getFunctor :: Heap s -> FunctorId -> ST s (String, Int)
getFunctor heap (FunctorId ident) = do
  interns <- readSTRef (heapInterns heap)
  case IM.lookup ident (functors interns) of
    Just value -> pure value
    Nothing -> error "Infera.Machine.Heap: missing interned functor"

constantEqual :: Constant -> Constant -> Bool
constantEqual (AtomConstant a) (AtomConstant b) = a == b
constantEqual (IntegerConstant a) (IntegerConstant b) = a == b
constantEqual (FloatConstant a) (FloatConstant b) = a == b
constantEqual (CharConstant a) (CharConstant b) = a == b
constantEqual (StringConstant a) (StringConstant b) = a == b
constantEqual _ _ = False

occursIn :: Heap s -> Address -> Address -> HeapM s Bool
occursIn heap variable root = visit IS.empty [root]
  where
    visit _ [] = pure False
    visit seen (address : rest) = do
      (target@(Address index _), cell) <- deref heap address
      if target == variable
        then pure True
        else if IS.member index seen
          then visit seen rest
          else case cell of
            Structure _ True _ -> visit (IS.insert index seen) rest
            Structure _ False arguments -> visit (IS.insert index seen) (arguments ++ rest)
            _ -> visit (IS.insert index seen) rest

-- | Occurs-checked unification, atomic on mismatch and invalid handles.
-- Variable aliasing points the newer allocation at the older allocation.
-- No same-address shortcut applies to constants or structures: NaN does not
-- unify with itself, even when nested in a shared structure.
unify :: Heap s -> Address -> Address -> ST s (Either HeapError Bool)
unify heap left right = fmap (fmap fst) (unifyWithChanges compare heap left right)

-- | Unify using the caller's stable variable ordering, returning every
-- reference written by a successful operation. Logical IDs can be allocated
-- out of order after an opaque sub-search, so an embedding must not assume
-- allocation age is always its variable order. Failed operations return no
-- changes and restore the heap and trail atomically.
unifyWithChanges :: (Address -> Address -> Ordering) -> Heap s -> Address -> Address -> ST s (Either HeapError (Bool, [Address]))
unifyWithChanges order heap left right = do
  mark <- checkpoint heap
  result <- unifyWithChangesInTransaction order heap left right
  case result of
    Right (True, _) -> pure result
    _ -> do
      restored <- rollback heap mark
      pure $ case restored of
        Left err -> Left err
        Right () -> result

-- | Trusted internal unification under a transaction owned by the caller.
-- This runs exactly the ordinary occurs-checked unifier and trails every
-- write, but does not create a nested checkpoint or roll back on failure.
-- A mismatch or heap error can therefore leave partial writes installed.
-- The enclosing transaction must restore its checkpoint before exposing any
-- failed result. Use 'unifyWithChanges' when that ownership proof is absent.
--
-- Compiled whole-head matching calls this only inside Machine.CLP.unifyUsing,
-- whose transaction owns every leaf write; activation also owns an outer
-- checkpoint covering source-root and constructor allocations.
unifyWithChangesInTransaction :: (Address -> Address -> Ordering) -> Heap s -> Address -> Address
  -> ST s (Either HeapError (Bool, [Address]))
unifyWithChangesInTransaction order heap left right = runExceptT (loop [] [(left, right)])
  where
    loop changed [] = pure (True, reverse changed)
    loop changed ((a, b) : rest) = do
      (a', ac) <- deref heap a
      (b', bc) <- deref heap b
      case (ac, bc) of
        (Ref _, Ref _)
          | a' == b' -> loop changed rest
          | order a' b' == GT -> writeCell heap a' (Ref b') >> loop (a' : changed) rest
          | otherwise -> writeCell heap b' (Ref a') >> loop (b' : changed) rest
        (Ref _, _) -> bind changed a' b' bc rest
        (_, Ref _) -> bind changed b' a' ac rest
        (Con ai, Con bi) -> do
          av <- lift (getConstant heap ai)
          bv <- lift (getConstant heap bi)
          if constantEqual av bv then loop changed rest else pure (False, [])
        (Structure af _ as, Structure bf _ bs)
          | af == bf -> loop changed (zip as bs ++ rest)
        _ -> pure (False, [])
    bind changed variable target cell rest = do
      cyclic <- case cell of
        Con _ -> pure False
        Structure _ True _ -> pure False
        _ -> occursIn heap variable target
      if cyclic
        then pure (False, [])
        else writeCell heap variable (Ref target) >> loop (variable : changed) rest

-- | Export roots as ordinary immutable terms. Free variables are numbered in
-- first-occurrence order across the entire root list, preserving all aliases.
-- Source VarIds are activation-local names, not heap variable identities.
exportTerms :: Heap s -> [Address] -> ST s (Either HeapError [Term])
exportTerms heap roots = runExceptT $ fst <$> exportMany Map.empty roots
  where
    exportMany variables [] = pure ([], variables)
    exportMany variables (root : rest) = do
      (term, next) <- exportOne variables root
      (terms, final) <- exportMany next rest
      pure (term : terms, final)
    exportOne variables root = do
      (address, cell) <- deref heap root
      case cell of
        Ref _ -> case Map.lookup address variables of
          Just variable -> pure (Var variable, variables)
          Nothing -> do
            let variable = Map.size variables :: VarId
            pure (Var variable, Map.insert address variable variables)
        Con ident -> do
          scalar <- lift (getConstant heap ident)
          let term = case scalar of
                AtomConstant value -> Atom value
                IntegerConstant value -> IntLit value
                FloatConstant value -> FloatLit value
                CharConstant value -> CharLit value
                StringConstant value -> StrLit value
          pure (term, variables)
        Structure ident _ arguments -> do
          (name, _) <- lift (getFunctor heap ident)
          (terms, next) <- exportMany variables arguments
          pure (Compound name terms, next)

exportTerm :: Heap s -> Address -> ST s (Either HeapError Term)
exportTerm heap address = do
  result <- exportTerms heap [address]
  pure $ case result of
    Right [term] -> Right term
    Left err -> Left err
    Right _ -> error "Infera.Machine.Heap: impossible export arity"
