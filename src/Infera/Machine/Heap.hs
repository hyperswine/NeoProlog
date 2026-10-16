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
-- path compression, rational-tree unification, collector or control stack yet.
module Infera.Machine.Heap
  ( Heap,
    FrozenHeap,
    Address,
    Environment,
    Checkpoint,
    HeapError (..),
    newHeap,
    thawHeap,
    freezeHeap,
    emptyEnvironment,
    newVariable,
    importTerm,
    importWithEnvironment,
    exportTerm,
    exportTerms,
    dereference,
    unify,
    checkpoint,
    rollback,
    heapSize,
    trailSize,
  )
where

import Control.Monad (forM_, unless, when)
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
  deriving (Eq, Show)

newtype Environment = Environment (IntMap Address)

emptyEnvironment :: Environment
emptyEnvironment = Environment IM.empty

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
  | Structure !FunctorId [Address]

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

thawHeap :: FrozenHeap -> ST s (Heap s)
thawHeap (FrozenHeap cells trail interns serial) =
  Heap <$> thawPaged cells <*> thawPaged trail <*> newSTRef interns <*> newSTRef serial

freezeHeap :: Heap s -> ST s FrozenHeap
freezeHeap heap =
  FrozenHeap <$> freezePaged (heapCells heap) <*> freezePaged (heapTrail heap)
    <*> readSTRef (heapInterns heap) <*> readSTRef (nextSerial heap)

heapSize :: Heap s -> ST s Int
heapSize = readSTRef . pagedTop . heapCells

trailSize :: Heap s -> ST s Int
trailSize = readSTRef . pagedTop . heapTrail

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

-- | Instantiate into an explicit activation environment. Share the returned
-- environment when importing a clause head and its body or several roots.
importWithEnvironment :: Heap s -> Environment -> Term -> ST s (Either HeapError (Address, Environment))
importWithEnvironment heap (Environment initial) term = atomic heap $ do
  -- Validate even unused entries, so a discarded environment cannot appear
  -- to work until one particular source variable happens to be encountered.
  forM_ (IM.elems initial) (readCell heap)
  (address, environment) <- importInto initial term
  pure (address, Environment environment)
  where
    importInto environment (Var variable) = case IM.lookup variable environment of
      Just address -> pure (address, environment)
      Nothing -> do
        address <- allocate heap Ref
        pure (address, IM.insert variable address environment)
    importInto environment (Compound name arguments) = do
      (addresses, final) <- importArguments environment arguments
      ident <- lift (internFunctor heap name (length addresses))
      address <- allocate heap (const (Structure ident addresses))
      pure (address, final)
    importInto environment scalar = do
      (key, value) <- case scalar of
        Atom value -> pure (AtomKey value, AtomConstant value)
        IntLit value -> pure (IntegerKey value, IntegerConstant value)
        FloatLit value -> pure (FloatKey (castDoubleToWord64 value), FloatConstant value)
        CharLit value -> pure (CharKey value, CharConstant value)
        StrLit value -> pure (StringKey value, StringConstant value)
      ident <- lift (internConstant heap key value)
      address <- allocate heap (const (Con ident))
      pure (address, environment)
    importArguments environment [] = pure ([], environment)
    importArguments environment (argument : rest) = do
      (address, next) <- importInto environment argument
      (addresses, final) <- importArguments next rest
      pure (address : addresses, final)

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
            Structure _ arguments -> visit (IS.insert index seen) (arguments ++ rest)
            _ -> visit (IS.insert index seen) rest

-- | Occurs-checked unification, atomic on mismatch and invalid handles.
-- Variable aliasing points the newer allocation at the older allocation.
-- No same-address shortcut applies to constants or structures: NaN does not
-- unify with itself, even when nested in a shared structure.
unify :: Heap s -> Address -> Address -> ST s (Either HeapError Bool)
unify heap left right = do
  mark <- checkpoint heap
  result <- runExceptT (loop [(left, right)])
  case result of
    Right True -> pure result
    _ -> do
      restored <- rollback heap mark
      pure $ case restored of
        Left err -> Left err
        Right () -> result
  where
    loop [] = pure True
    loop ((a, b) : rest) = do
      (a', ac) <- deref heap a
      (b', bc) <- deref heap b
      case (ac, bc) of
        (Ref _, Ref _)
          | a' == b' -> loop rest
          | a' > b' -> writeCell heap a' (Ref b') >> loop rest
          | otherwise -> writeCell heap b' (Ref a') >> loop rest
        (Ref _, _) -> bind a' b' rest
        (_, Ref _) -> bind b' a' rest
        (Con ai, Con bi) -> do
          av <- lift (getConstant heap ai)
          bv <- lift (getConstant heap bi)
          if constantEqual av bv then loop rest else pure False
        (Structure af as, Structure bf bs)
          | af == bf -> loop (zip as bs ++ rest)
        _ -> pure False
    bind variable target rest = do
      cyclic <- occursIn heap variable target
      if cyclic
        then pure False
        else writeCell heap variable (Ref target) >> loop rest

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
        Structure ident arguments -> do
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
