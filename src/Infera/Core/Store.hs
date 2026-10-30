{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | The core resolution store: tagged words in one growable pinned block,
-- a trail of addresses in a second, a boxed-constant table and interned
-- symbol tables.
--
-- Every value is one 'Int' word whose low three bits are a tag:
--
-- > REF  address of a cell; an unbound variable references itself
-- > STR  address of a functor cell, followed by that many argument cells
-- > FUN  functor id and arity, only ever found at the head of a structure
-- > INT  immediate signed integer (61 bits)
-- > ATM  atom id
-- > BOX  index into the boxed table: bignums, floats and strings
-- > CHR  character code point
--
-- The heap, trail and bound-log blocks are pinned 'ForeignPtr' allocations
-- owned by 'IORef's, but the hot path never touches the 'IORef': each
-- block's base address (and capacity) is cached in an unboxed register
-- slot, so a cell access is one register read plus one memory operation,
-- and loops can hoist the base across iterations. A pointer read from a
-- slot ('cellsPtr', 'trailPtr', 'boundPtr') is invalidated by any growth
-- of that block; no pointer survives across an allocation that can grow.
-- Pinning also gives the JIT tier a stable address to hand to native code.
--
-- Binding writes one word. A binding is trailed only when the bound cell is
-- older than the newest choice point ('hb'), and backtracking restores the
-- heap top and unwinds the trail. Nothing is copied to save a branch.
module Infera.Core.Store
  ( -- * Words
    Word',
    tagRef, tagStr, tagFun, tagInt, tagAtm, tagBox, tagChr,
    tagOf, valOf, mkWord, refWord, strWord, funWord, funId, funArity, funKey, funGround, groundBit,
    intWord, atmWord, boxWord, chrWord, fitsImmediate,
    -- * Boxed constants and symbols
    Boxed (..),
    Symbols (..),
    newSymbols, internAtom, internFunctor, atomName, functorName,
    -- * The machine store
    Store (..),
    newStore,
    heapTop, setHeapTop, trailTop, setTrailTop, hb, setHb,
    outLen, setOutLen, arithData, bumpArithData, freshId, setFreshId,
    readCell, writeCell, pushCell, allocCells, allocSlots, allocFrame, operandWord, operandAt,
    resetSlots, resetFrame, markerWord, logicalId, nameCell, nameCellAs,
    replaceLogicalIds, collectionStats, recordCollection,
    readArg, writeArg, saveArgs, loadArgs, reserveCells, groundNowWord,
    readReg, writeReg, rVAL, rGCLIM, rCLP, rBOUND, rCAP, rTRAILCAP, initialCollectLimit, markerVars,
    drainBound, recordBoundCell,
    -- * Pinned block pointers (invalidated by growth)
    cellsPtr, trailPtr, boundPtr, peekAt, pokeAt,
    deref, bind, unwindTrail, trailIf, trailValueIf,
    structureWord, structure2, structure2WithGround,
    box, boxed, boxIn, boxedIn,
    -- * Unification and equality
    unify, equiv, isGroundWord, occursIn,
    -- * Term exchange
    importTerm, importTermWords, exportTerm, exportTermWith,
  )
where

import Control.Concurrent.MVar (MVar, newMVar, withMVar)
import Control.Monad (when)
import Data.Array.Base (getNumElements, unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, IOUArray, newArray, newArray_)
import Data.Bits (complement, shiftL, shiftR, (.&.), (.|.))
import Data.IORef
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import Foreign.ForeignPtr (ForeignPtr, mallocForeignPtrBytes)
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import Foreign.Ptr (Ptr, intPtrToPtr, plusPtr, ptrToIntPtr)
import Foreign.Storable (peek, poke, sizeOf)
import Infera.Syntax (Term (..), VarId)

type Word' = Int

tagRef, tagStr, tagFun, tagInt, tagAtm, tagBox, tagChr :: Int
tagRef = 0
tagStr = 1
tagFun = 2
tagInt = 3
tagAtm = 4
tagBox = 5
tagChr = 6

tagOf :: Word' -> Int
tagOf w = w .&. 7
{-# INLINE tagOf #-}

valOf :: Word' -> Int
valOf w = w `shiftR` 3
{-# INLINE valOf #-}

mkWord :: Int -> Int -> Word'
mkWord tag v = (v `shiftL` 3) .|. tag
{-# INLINE mkWord #-}

refWord, strWord, atmWord, boxWord, chrWord :: Int -> Word'
refWord = mkWord tagRef
strWord = mkWord tagStr
atmWord = mkWord tagAtm
boxWord = mkWord tagBox
chrWord = mkWord tagChr
{-# INLINE refWord #-}
{-# INLINE strWord #-}

intWord :: Int -> Word'
intWord = mkWord tagInt
{-# INLINE intWord #-}

-- | Functor words pack the arity in the low 19 bits of the value; the next
-- bit is the ground memo: set once the structure has been found ground.
funWord :: Int -> Int -> Word'
funWord fid arity = mkWord tagFun ((fid `shiftL` 20) .|. arity)
{-# INLINE funWord #-}

funId :: Word' -> Int
funId w = valOf w `shiftR` 20
{-# INLINE funId #-}

funArity :: Word' -> Int
funArity w = valOf w .&. 0x7FFFF
{-# INLINE funArity #-}

groundBit :: Int
groundBit = 1 `shiftL` 22

-- | The functor word without its ground memo, for comparisons and keys.
funKey :: Word' -> Word'
funKey w = w .&. complement groundBit
{-# INLINE funKey #-}

funGround :: Word' -> Bool
funGround w = w .&. groundBit /= 0
{-# INLINE funGround #-}

fitsImmediate :: Integer -> Bool
fitsImmediate n = n >= -(2 ^ (60 :: Int)) && n < 2 ^ (60 :: Int)
{-# INLINE fitsImmediate #-}

data Boxed = BInt !Integer | BFlt !Double | BStr !String
  deriving (Eq, Show)

-- | Atom, functor and boxed-constant tables. Compilation interns everything a
-- program and query mention; builtins intern the rare constant they create at
-- runtime. A compiled plan bakes these ids into words, so the tables are
-- program-scoped: every query's store shares the tables of the program it
-- runs, and the tables only ever grow. Interning takes the lock because a
-- store may be built and run from more than one thread; the read paths
-- ('atomName', 'functorName', 'boxed') do not.
data Symbols = Symbols
  { atomIds :: !(IORef (Map.Map String Int)),
    atomNames :: !(IORef (IM.IntMap String)),
    functorIds :: !(IORef (Map.Map (String, Int) Int)),
    functorNames :: !(IORef (IM.IntMap (String, Int))),
    -- | bignums, floats and strings referenced by @BOX@ words
    boxTable :: !(IORef (IOArray Int Boxed)),
    boxCount :: !(IORef Int),
    symbolLock :: !(MVar ())
  }

newSymbols :: IO Symbols
newSymbols =
  Symbols <$> newIORef Map.empty <*> newIORef IM.empty <*> newIORef Map.empty <*> newIORef IM.empty
    <*> (newArray_ (0, 255) >>= newIORef) <*> newIORef 0 <*> newMVar ()

-- | Grow a shared table under its lock, publishing the new table before the
-- count that indexes it.
internAtom :: Symbols -> String -> IO Int
internAtom symbols name = withMVar (symbolLock symbols) $ const $ do
  ids <- readIORef (atomIds symbols)
  case Map.lookup name ids of
    Just i -> pure i
    Nothing -> do
      let i = Map.size ids
      writeIORef (atomIds symbols) (Map.insert name i ids)
      modifyIORef' (atomNames symbols) (IM.insert i name)
      pure i

internFunctor :: Symbols -> String -> Int -> IO Int
internFunctor symbols name arity = withMVar (symbolLock symbols) $ const $ do
  ids <- readIORef (functorIds symbols)
  case Map.lookup (name, arity) ids of
    Just i -> pure i
    Nothing -> do
      let i = Map.size ids
      writeIORef (functorIds symbols) (Map.insert (name, arity) i ids)
      modifyIORef' (functorNames symbols) (IM.insert i (name, arity))
      pure i

atomName :: Symbols -> Int -> IO String
atomName symbols i = (IM.! i) <$> readIORef (atomNames symbols)

functorName :: Symbols -> Int -> IO (String, Int)
functorName symbols i = (IM.! i) <$> readIORef (functorNames symbols)

-- Register slots of the unboxed register file. Slot 4 is unused: the boxed
-- constant count moved into the program-scoped 'Symbols'.
rH, rTR, rHB, rOUT, rARITH, rFRESH, rCAP, rVAL :: Int
rH = 0
rTR = 1
rHB = 2
rOUT = 3
rARITH = 5
rFRESH = 6
rCAP = 7
-- | scratch result register of the integer fast path
rVAL = 8

-- | heap size (cells) above which the next call collects
rGCLIM :: Int
rGCLIM = 9

-- | non-zero once constraints exist: bindings are recorded for the store
rCLP :: Int
rCLP = 10

-- | number of recorded bindings awaiting reconciliation
rBOUND :: Int
rBOUND = 11

-- Register 12 is one past the highest named address (pruning on a lower
-- heap top is needed only below it); registers 13-15 are GC counters.
rIDENT, rGCCOUNT, rGCLIVE, rGCRECLAIM :: Int
rIDENT = 12
rGCCOUNT = 13
rGCLIVE = 14
rGCRECLAIM = 15

-- Pinned-block cache slots. These hold a block's base address (as an
-- 'Int'; see 'ptrAsInt') and, where growth needs it, its capacity in
-- cells, so the hot path reads unboxed memory instead of an 'IORef' and
-- loops can hoist the base across iterations. The 'ForeignPtr' that owns
-- each block lives behind an 'IORef' and is touched only on growth (cold).
-- A pointer read from one of these slots is invalidated by any growth of
-- that block: it must not be cached across an operation that allocates.
rCELLS, rTRAILB, rTRAILCAP, rBOUNDP, rBOUNDCAP :: Int
rCELLS = 16
rTRAILB = 17
rTRAILCAP = 18
rBOUNDP = 19
rBOUNDCAP = 20

initialCollectLimit :: Int
initialCollectLimit = 262144

readReg :: Store -> Int -> IO Int
readReg s = unsafeRead (regs s)
{-# INLINE readReg #-}

writeReg :: Store -> Int -> Int -> IO ()
writeReg s = unsafeWrite (regs s)
{-# INLINE writeReg #-}

-- | The store's blocks. The 'IORef's own the pinned 'ForeignPtr's (cold
-- path only); the register slots above cache their base addresses.
data Store = Store
  { cellsFP :: !(IORef (ForeignPtr Int)),
    trailFP :: !(IORef (ForeignPtr Int)),
    regs :: !(IOUArray Int Int),
    -- | argument registers of the call being made
    argRegs :: !(IOUArray Int Int),
    boundFP :: !(IORef (ForeignPtr Int)),
    -- | The names of the variable cells that have left the heap, by
    -- address (see 'nameCell').
    logicalIds :: !(IORef (IM.IntMap Int)),
    symbols :: !Symbols
  }

wordBytes :: Int
wordBytes = sizeOf (undefined :: Int)

-- | A pinned block of @n@ words. The address is stable (this is what the
-- JIT tier will hand to native code); the 'ForeignPtr' owns the memory.
pinnedBlock :: Int -> IO (ForeignPtr Int, Ptr Int)
pinnedBlock n = do
  fp <- mallocForeignPtrBytes (n * wordBytes)
  pure (fp, unsafeForeignPtrToPtr fp)

ptrAsInt :: Ptr Int -> Int
ptrAsInt = fromIntegral . ptrToIntPtr
{-# INLINE ptrAsInt #-}

intAsPtr :: Int -> Ptr Int
intAsPtr = intPtrToPtr . fromIntegral
{-# INLINE intAsPtr #-}

-- Cells are never read before they are written, so the block need not be
-- initialised; untouched pages cost nothing.
initialCells :: Int
initialCells = 1048576

initialTrail, initialBound :: Int
initialTrail = 4096
initialBound = 256

newStore :: Symbols -> IO Store
newStore syms = do
  (csFP, csP) <- pinnedBlock initialCells
  (trFP, trP) <- pinnedBlock initialTrail
  rs <- newArray (0, 31) 0
  ar <- newArray (0, 4095) 0
  (bdFP, bdP) <- pinnedBlock initialBound
  unsafeWrite rs rCAP initialCells
  unsafeWrite rs rGCLIM initialCollectLimit
  unsafeWrite rs rCELLS (ptrAsInt csP)
  unsafeWrite rs rTRAILB (ptrAsInt trP)
  unsafeWrite rs rTRAILCAP initialTrail
  unsafeWrite rs rBOUNDP (ptrAsInt bdP)
  unsafeWrite rs rBOUNDCAP initialBound
  Store <$> newIORef csFP <*> newIORef trFP <*> pure rs <*> pure ar
    <*> newIORef bdFP <*> newIORef IM.empty <*> pure syms

-- | The current cells base pointer. Invalidated by any growth of the
-- cells block: never cache it across an operation that allocates cells.
cellsPtr :: Store -> IO (Ptr Int)
cellsPtr s = intAsPtr <$> unsafeRead (regs s) rCELLS
{-# INLINE cellsPtr #-}

-- | The current trail base pointer; same invalidation rule as 'cellsPtr'.
trailPtr :: Store -> IO (Ptr Int)
trailPtr s = intAsPtr <$> unsafeRead (regs s) rTRAILB
{-# INLINE trailPtr #-}

-- | The current bound-log base pointer; same invalidation rule as
-- 'cellsPtr'.
boundPtr :: Store -> IO (Ptr Int)
boundPtr s = intAsPtr <$> unsafeRead (regs s) rBOUNDP
{-# INLINE boundPtr #-}

-- | Read one word from a pinned block. The same unchecked discipline as
-- 'Data.Array.Base.unsafeRead': the caller guarantees the index is within
-- the block's current capacity.
peekAt :: Ptr Int -> Int -> IO Int
peekAt p i = peek (p `plusPtr` (i * wordBytes))
{-# INLINE peekAt #-}

-- | Write one word to a pinned block; unchecked like 'peekAt'.
pokeAt :: Ptr Int -> Int -> Int -> IO ()
pokeAt p i w = poke (p `plusPtr` (i * wordBytes)) w
{-# INLINE pokeAt #-}

readArg :: Store -> Int -> IO Word'
readArg s = unsafeRead (argRegs s)
{-# INLINE readArg #-}

writeArg :: Store -> Int -> Word' -> IO ()
writeArg s = unsafeWrite (argRegs s)
{-# INLINE writeArg #-}

-- | Copy the first @n@ argument registers to the heap for a choice point;
-- returns the address of the copy.
saveArgs :: Store -> Int -> IO Int
saveArgs s n = do
  top <- heapTop s
  ensureCells s (top + n)
  cells <- cellsPtr s
  let go !i
        | i >= n = pure ()
        | otherwise = unsafeRead (argRegs s) i >>= pokeAt cells (top + i) >> go (i + 1)
  go 0
  unsafeWrite (regs s) rH (top + n)
  pure top

loadArgs :: Store -> Int -> Int -> IO ()
loadArgs s addr n = do
  cells <- cellsPtr s
  let go !i
        | i >= n = pure ()
        | otherwise = peekAt cells (addr + i) >>= unsafeWrite (argRegs s) i >> go (i + 1)
  go 0

heapTop, trailTop, hb, outLen, arithData, freshId :: Store -> IO Int
heapTop s = unsafeRead (regs s) rH
trailTop s = unsafeRead (regs s) rTR
hb s = unsafeRead (regs s) rHB
outLen s = unsafeRead (regs s) rOUT
arithData s = unsafeRead (regs s) rARITH
-- | The next unused variable name. It never moves back within a query.
freshId s = unsafeRead (regs s) rFRESH
{-# INLINE heapTop #-}
{-# INLINE trailTop #-}
{-# INLINE hb #-}
{-# INLINE freshId #-}

setHeapTop, setTrailTop, setHb, setOutLen, setFreshId :: Store -> Int -> IO ()
setHeapTop s top = do
  -- Only detached slots have sparse identities. Backtracking must discard
  -- identities above its heap mark before those addresses are reused.
  boundary <- unsafeRead (regs s) rIDENT
  when (top < boundary) $ do
    modifyIORef' (logicalIds s) (fst . IM.split top)
    unsafeWrite (regs s) rIDENT top
  unsafeWrite (regs s) rH top
setTrailTop s = unsafeWrite (regs s) rTR
setHb s = unsafeWrite (regs s) rHB
setOutLen s = unsafeWrite (regs s) rOUT
setFreshId s = unsafeWrite (regs s) rFRESH
{-# INLINE setHeapTop #-}
{-# INLINE setTrailTop #-}
{-# INLINE setHb #-}
{-# INLINE setFreshId #-}

-- | Count arithmetic structures constructed as data. While it is zero, no
-- call argument can contain one and the normalisation walk is skipped.
bumpArithData :: Store -> IO ()
bumpArithData s = unsafeRead (regs s) rARITH >>= unsafeWrite (regs s) rARITH . (+ 1)

readCell :: Store -> Int -> IO Word'
readCell s i = do
  p <- cellsPtr s
  peekAt p i
{-# INLINE readCell #-}

writeCell :: Store -> Int -> Word' -> IO ()
writeCell s i w = do
  p <- cellsPtr s
  pokeAt p i w
{-# INLINE writeCell #-}

ensureCells :: Store -> Int -> IO ()
ensureCells s needed = do
  capacity <- unsafeRead (regs s) rCAP
  when (needed > capacity) (growCells s needed)
{-# INLINE ensureCells #-}

growCells :: Store -> Int -> IO ()
growCells s needed = do
  capacity <- unsafeRead (regs s) rCAP
  size' <- pure (max needed (capacity * 4))
  (fp', p') <- pinnedBlock size'
  old <- cellsPtr s
  top <- heapTop s
  let copy !i
        | i >= top = pure ()
        | otherwise = peekAt old i >>= pokeAt p' i >> copy (i + 1)
  copy 0
  writeIORef (cellsFP s) fp'
  unsafeWrite (regs s) rCELLS (ptrAsInt p')
  unsafeWrite (regs s) rCAP size'

-- | Append one word and return its address.
pushCell :: Store -> Word' -> IO Int
pushCell s w = do
  top <- heapTop s
  ensureCells s (top + 1)
  writeCell s top w
  unsafeWrite (regs s) rH (top + 1)
  pure top
{-# INLINE pushCell #-}

-- | Reserve @n@ cells without initialising them; the caller writes each one
-- before anything reads it.
reserveCells :: Store -> Int -> IO Int
reserveCells s n = do
  top <- heapTop s
  ensureCells s (top + n)
  unsafeWrite (regs s) rH (top + n)
  pure top
{-# INLINE reserveCells #-}

-- | Is this word ground right now (unbound cells are not; structures use
-- their memo only)?
groundNowWord :: Store -> Word' -> IO Bool
groundNowWord s w = case tagOf w of
  t | t == tagRef -> do
        d <- deref s w
        if tagOf d == tagRef then pure False else groundNowWord s d
    | t == tagStr -> funGround <$> readCell s (valOf w)
    | otherwise -> pure True
{-# INLINE groundNowWord #-}

-- | Reserve @n@ unbound variable cells and return the first address.
allocCells :: Store -> Int -> IO Int
allocCells s n = do
  top <- heapTop s
  ensureCells s (top + n)
  p <- cellsPtr s
  let go !i
        | i >= top + n = pure ()
        | otherwise = pokeAt p i (refWord i) >> go (i + 1)
  go top
  unsafeWrite (regs s) rH (top + n)
  pure top

-- | A marker cell precedes every block of activation variables. Functor
-- words never occur as values, so a marker is unambiguous when scanning
-- down from a variable cell. It packs the block size above bit 40, which
-- tail-call frame reuse reads as the block's capacity. Variable identity
-- is not positional: see 'nameCell'.
markerWord :: Int -> Word'
markerWord n = mkWord tagFun (n `shiftL` 40)
{-# INLINE markerWord #-}

markerVars :: Word' -> Int
markerVars w = valOf w `shiftR` 40

-- | Reserve @n@ variable cells preceded by a marker; returns the address of
-- the first variable.
allocSlots :: Store -> Int -> IO Int
allocSlots s n = do
  top <- heapTop s
  ensureCells s (top + n + 1)
  p <- cellsPtr s
  pokeAt p top (markerWord n)
  let go !i
        | i > top + n = pure ()
        | otherwise = pokeAt p i (refWord i) >> go (i + 1)
  go (top + 1)
  unsafeWrite (regs s) rH (top + n + 1)
  pure (top + 1)
{-# INLINE allocSlots #-}

-- | Allocate a clause activation, clearing only the supplied variable
-- offsets. Every omitted slot must be written by its first head occurrence
-- before a matcher or head constructor reads it. The compiled layout is
-- shared across calls; stable logical-variable allocations use 'allocSlots'.
allocFrame :: Store -> Int -> [Int] -> IO Int
allocFrame s count initialize = do
  top <- heapTop s
  ensureCells s (top + count + 1)
  p <- cellsPtr s
  pokeAt p top (markerWord count)
  let base = top + 1
      go [] = pure ()
      go (offset : offsets) = do
        let addr = base + offset
        pokeAt p addr (refWord addr)
        go offsets
  go initialize
  unsafeWrite (regs s) rH (top + count + 1)
  pure base
{-# INLINE allocFrame #-}

-- | Read an activation operand without exposing its storage cell. A value
-- already installed in the slot can be shared directly; a still-unbound
-- local must first acquire a stable variable cell outside the reusable
-- activation. Redirecting the operand is an ordinary binding, so an older
-- choice restores its self-reference before reclaiming the promoted cell.
--
-- Query cells and captured 'PWord' operands are logical variables already:
-- callers pass only the addresses of live activation operands here.
operandWord :: Store -> Int -> IO Word'
operandWord s addr = do
  value <- readCell s addr >>= deref s
  if value == refWord addr
    then do
      stable <- allocCells s 1
      let word = refWord stable
      bind s addr word
      pure word
    else pure value
{-# INLINE operandWord #-}

-- | The operand accessor for a fresh contiguous activation. Captured plans
-- detached by collection use ready words instead, and must never call this
-- function with a dummy base.
operandAt :: Store -> Int -> Int -> IO Word'
operandAt s base offset = do
  let addr = base + offset
  -- Non-self references were installed from already stable operands. They
  -- can be passed on as references: eagerly dereferencing here adds a walk
  -- that the consuming matcher/builtin would otherwise perform once.
  value <- readCell s addr
  if value == refWord addr
    then do
      stable <- allocCells s 1
      let word = refWord stable
      bind s addr word
      pure word
    else pure value
{-# INLINE operandAt #-}

-- | Reinitialize an otherwise unreachable activation for a tail call.
-- The caller must prove that every slot is at or above the newest choice
-- boundary, and that no argument, continuation, constraint or live term
-- refers to these operand cells. Escaped logical variables have their own
-- cells, allocated by 'operandWord'. The physical capacity may exceed the
-- next clause's variable count; unused slots remain inaccessible.
resetSlots :: Store -> Int -> Int -> IO ()
resetSlots s base capacity = resetFrame s base capacity [0 .. capacity - 1]
{-# INLINE resetSlots #-}

-- | Reset an unreachable tail activation with a compiled initialization
-- layout. The reachability and choice-boundary requirements of 'resetSlots'
-- apply. Omitted offsets must be initialized by first head occurrences before
-- they are read, exactly as for 'allocFrame'.
resetFrame :: Store -> Int -> Int -> [Int] -> IO ()
resetFrame s base capacity initialize = do
  -- An unbound operand is promoted before it escapes, so its slot is not
  -- normally named. Forget any name in the range all the same: a reused
  -- address is a different variable.
  boundary <- unsafeRead (regs s) rIDENT
  when (base < boundary) $ do
    ids <- readIORef (logicalIds s)
    case IM.lookupGE base ids of
      Just (addr, _) | addr < base + capacity ->
        let (before, _, remaining) = IM.splitLookup base ids
            (_, _, after) = IM.splitLookup (base + capacity - 1) remaining
         in writeIORef (logicalIds s) (IM.union before after)
      _ -> pure ()
  p <- cellsPtr s
  pokeAt p (base - 1) (markerWord capacity)
  let go [] = pure ()
      go (offset : offsets) = do
        let addr = base + offset
        pokeAt p addr (refWord addr)
        go offsets
  go initialize
{-# INLINE resetFrame #-}

-- | The name of a variable cell, if it has one. Query cells are named by
-- the caller; any other cell is named when it first leaves the heap (an
-- export, a constraint, a copy), and keeps that name while it lives.
logicalId :: Store -> Int -> IO (Maybe Int)
logicalId s addr = IM.lookup addr <$> readIORef (logicalIds s)
{-# INLINE logicalId #-}

-- | The name of a variable cell, giving it the next fresh one if it has
-- none. Names are never reused within a query: the fresh counter does not
-- move back on backtracking, so a name that outlives its branch on a
-- surviving cell cannot collide with a later one.
nameCell :: Store -> Int -> IO Int
nameCell s addr = do
  known <- logicalId s addr
  case known of
    Just v -> pure v
    Nothing -> do
      v <- freshId s
      setFreshId s (v + 1)
      nameCellAs s addr v
      pure v

-- | Give a cell a known name: one the constraint store or a copied answer
-- already uses for this variable.
nameCellAs :: Store -> Int -> Int -> IO ()
nameCellAs s addr v = do
  modifyIORef' (logicalIds s) (IM.insert addr v)
  boundary <- unsafeRead (regs s) rIDENT
  when (addr >= boundary) (unsafeWrite (regs s) rIDENT (addr + 1))
  current <- freshId s
  when (v >= current) (setFreshId s (v + 1))

-- | Install the names of the cells that survived a collection, at their
-- new addresses, below the supplied heap top.
replaceLogicalIds :: Store -> Int -> IM.IntMap Int -> IO ()
replaceLogicalIds s boundary ids = do
  writeIORef (logicalIds s) ids
  unsafeWrite (regs s) rIDENT boundary

-- | Collection count, cells retained by the last collection and total
-- reclaimed cells. These counters are outside the query's logical state.
collectionStats :: Store -> IO (Int, Int, Int)
collectionStats s = (,,) <$> readReg s rGCCOUNT <*> readReg s rGCLIVE <*> readReg s rGCRECLAIM

recordCollection :: Store -> Int -> Int -> IO ()
recordCollection s before after = do
  readReg s rGCCOUNT >>= writeReg s rGCCOUNT . (+ 1)
  writeReg s rGCLIVE after
  readReg s rGCRECLAIM >>= writeReg s rGCRECLAIM . (+ (before - after))

-- | Build a structure from a functor word and argument words, setting the
-- ground memo when every argument is ground now.
structureWord :: Store -> Word' -> [Word'] -> IO Word'
structureWord s functor args = do
  ground <- allGround args
  addr <- reserveCells s (funArity functor + 1)
  p <- cellsPtr s
  pokeAt p addr (if ground then functor .|. groundBit else functor)
  let fill !_ [] = pure ()
      fill !i (w : ws) = pokeAt p i w >> fill (i + 1) ws
  fill (addr + 1) args
  pure (strWord addr)
  where
    allGround [] = pure True
    allGround (w : ws) = do
      g <- groundNow w
      if g then allGround ws else pure False
    groundNow w = case tagOf w of
      t | t == tagRef -> do
            d <- deref s w
            if tagOf d == tagRef then pure False else groundNow d
        | t == tagStr -> funGround <$> readCell s (valOf w)
        | otherwise -> pure True

-- | The common two-argument constructor (including cons), with one heap
-- reservation and no intermediate argument list. Keep the raw references:
-- shallow control syntax and rollback depend on their identity.
structure2 :: Store -> Word' -> Word' -> Word' -> IO Word'
structure2 s functor a b = do
  ga <- groundNowWord s a
  ground <- if ga then groundNowWord s b else pure False
  structure2WithGround s functor ground a b
{-# INLINE structure2 #-}

-- | A constructor whose groundness is already known by its caller.
structure2WithGround :: Store -> Word' -> Bool -> Word' -> Word' -> IO Word'
structure2WithGround s functor ground a b = do
  addr <- reserveCells s 3
  p <- cellsPtr s
  pokeAt p addr (if ground then functor .|. groundBit else functor)
  pokeAt p (addr + 1) a
  pokeAt p (addr + 2) b
  pure (strWord addr)

-- | Follow reference chains. The result is either a non-REF word or the
-- REF of an unbound cell.
deref :: Store -> Word' -> IO Word'
deref s !w
  | tagOf w == tagRef = do
      p <- cellsPtr s
      let go !v = do
            v' <- peekAt p (valOf v)
            if v' == v || tagOf v' /= tagRef then pure v' else go v'
      go w
  | otherwise = pure w
{-# INLINE deref #-}

-- Trail entries: an even entry @2*addr@ resets the cell to unbound; an odd
-- entry @2*addr+1@ restores the word pushed just below it.
pushTrail :: Store -> Int -> IO ()
pushTrail s entry = do
  top <- trailTop s
  size <- unsafeRead (regs s) rTRAILCAP
  p <- trailPtr s
  p' <-
    if top < size
      then pure p
      else do
        let size' = size * 2
        (fp', p'') <- pinnedBlock size'
        let copy !i
              | i >= top = pure ()
              | otherwise = peekAt p i >>= pokeAt p'' i >> copy (i + 1)
        copy 0
        writeIORef (trailFP s) fp'
        unsafeWrite (regs s) rTRAILB (ptrAsInt p'')
        unsafeWrite (regs s) rTRAILCAP size'
        pure p''
  pokeAt p' top entry
  setTrailTop s (top + 1)

trailIf :: Store -> Int -> IO ()
trailIf s addr = do
  boundary <- hb s
  when (addr < boundary) (pushTrail s (addr * 2))
{-# INLINE trailIf #-}

-- | Record the previous word of a cell whose value changes in place (the
-- ground memo), so backtracking restores it.
trailValueIf :: Store -> Int -> Word' -> IO ()
trailValueIf s addr old = do
  boundary <- hb s
  when (addr < boundary) (pushTrail s old >> pushTrail s (addr * 2 + 1))
{-# INLINE trailValueIf #-}

-- | Bind the unbound cell at @addr@ to @w@. With constraints active the
-- address is recorded for the next reconciliation.
bind :: Store -> Int -> Word' -> IO ()
bind s addr w = do
  writeCell s addr w
  trailIf s addr
  flag <- unsafeRead (regs s) rCLP
  when (flag /= 0) (recordBound s addr)
{-# INLINE bind #-}

-- | Record a cell for reconciliation (used when relocating pending ones).
recordBoundCell :: Store -> Int -> IO ()
recordBoundCell = recordBound

recordBound :: Store -> Int -> IO ()
recordBound s addr = do
  top <- unsafeRead (regs s) rBOUND
  size <- unsafeRead (regs s) rBOUNDCAP
  p <- boundPtr s
  p' <-
    if top < size
      then pure p
      else do
        let size' = size * 2
        (fp', p'') <- pinnedBlock size'
        let copy !i
              | i >= top = pure ()
              | otherwise = peekAt p i >>= pokeAt p'' i >> copy (i + 1)
        copy 0
        writeIORef (boundFP s) fp'
        unsafeWrite (regs s) rBOUNDP (ptrAsInt p'')
        unsafeWrite (regs s) rBOUNDCAP size'
        pure p''
  pokeAt p' top addr
  unsafeWrite (regs s) rBOUND (top + 1)

-- | Take the recorded bindings, oldest first, and clear the record.
drainBound :: Store -> IO [Int]
drainBound s = do
  top <- unsafeRead (regs s) rBOUND
  p <- boundPtr s
  addrs <- mapM (peekAt p) [0 .. top - 1]
  unsafeWrite (regs s) rBOUND 0
  pure addrs

-- | Reset every trailed cell above @mark@ to unbound and restore the mark.
-- No allocation happens here, so both block bases are cached for the walk.
unwindTrail :: Store -> Int -> IO ()
unwindTrail s mark = do
  top <- trailTop s
  tr <- trailPtr s
  cells <- cellsPtr s
  let go !i
        | i < mark = pure ()
        | otherwise = do
            entry <- peekAt tr i
            if even entry
              then do
                let addr = entry `shiftR` 1
                pokeAt cells addr (refWord addr)
                go (i - 1)
              else do
                old <- peekAt tr (i - 1)
                pokeAt cells (entry `shiftR` 1) old
                go (i - 2)
  go (top - 1)
  setTrailTop s mark

-- | Append a constant to the program's boxed table. The table is shared by
-- every query's store, so a @BOX@ word compiled at load time means the same
-- value in every run; growth publishes the new table before the count that
-- indexes it.
box :: Store -> Boxed -> IO Word'
box s = boxIn (symbols s)

boxIn :: Symbols -> Boxed -> IO Word'
boxIn syms value = withMVar (symbolLock syms) $ const $ do
  table <- readIORef (boxTable syms)
  top <- readIORef (boxCount syms)
  size <- getNumElements table
  table' <-
    if top < size
      then pure table
      else do
        grown <- newArray_ (0, size * 2 - 1)
        let copy !i
              | i >= top = pure ()
              | otherwise = unsafeRead table i >>= unsafeWrite grown i >> copy (i + 1)
        copy 0
        writeIORef (boxTable syms) grown
        pure grown
  unsafeWrite table' top value
  writeIORef (boxCount syms) (top + 1)
  pure (boxWord top)

boxed :: Store -> Word' -> IO Boxed
boxed s = boxedIn (symbols s)

boxedIn :: Symbols -> Word' -> IO Boxed
boxedIn syms w = do
  table <- readIORef (boxTable syms)
  unsafeRead table (valOf w)
{-# INLINE boxedIn #-}

-- | Unify two words. Bindings made before a failure stay on the trail and
-- are undone by the caller's backtracking, exactly as in a WAM.
unify :: Store -> Word' -> Word' -> IO Bool
unify s a0 b0 = do
  a <- deref s a0
  b <- deref s b0
  if a == b
    then pure True
    else case (tagOf a, tagOf b) of
      (ta, tb)
        | ta == tagRef && tb == tagRef -> do
            -- Bind the younger cell to the older one, as a WAM does: the
            -- older cell outlives it on backtracking and collection keeps
            -- address order, so no reference can outlive its target.
            if valOf a > valOf b
              then bind s (valOf a) b >> pure True
              else bind s (valOf b) a >> pure True
        | ta == tagRef -> bindChecked (valOf a) b tb
        | tb == tagRef -> bindChecked (valOf b) a ta
        | ta == tagStr && tb == tagStr -> do
            fa <- readCell s (valOf a)
            fb <- readCell s (valOf b)
            if funKey fa /= funKey fb
              then pure False
              else args (valOf a + 1) (valOf b + 1) (funArity fa)
        | ta == tagBox && tb == tagBox -> do
            x <- boxed s a
            y <- boxed s b
            pure (sameBoxed x y)
        | otherwise -> pure False
  where
    -- Cyclic bindings fail: the language keeps the occurs check.
    bindChecked addr value tag
      | tag == tagStr = do
          cyclic <- occursIn s addr value
          if cyclic then pure False else bind s addr value >> pure True
      | otherwise = bind s addr value >> pure True
    args !i !j !n
      | n == 0 = pure True
      | otherwise = do
          x <- readCell s i
          y <- readCell s j
          ok <- unify s x y
          if ok then args (i + 1) (j + 1) (n - 1) else pure False

-- Floats unify by value: signed zeros unify, NaN never unifies with itself.
sameBoxed :: Boxed -> Boxed -> Bool
sameBoxed (BInt x) (BInt y) = x == y
sameBoxed (BFlt x) (BFlt y) = x == y
sameBoxed (BStr x) (BStr y) = x == y
sameBoxed _ _ = False

-- | Structural equality without binding (the @==@ builtin). Distinct
-- unbound variables are different.
equiv :: Store -> Word' -> Word' -> IO Bool
equiv s a0 b0 = do
  a <- deref s a0
  b <- deref s b0
  if a == b
    then pure True
    else case (tagOf a, tagOf b) of
      (ta, tb)
        | ta == tagStr && tb == tagStr -> do
            fa <- readCell s (valOf a)
            fb <- readCell s (valOf b)
            if funKey fa /= funKey fb then pure False else args (valOf a + 1) (valOf b + 1) (funArity fa)
        | ta == tagBox && tb == tagBox -> sameBoxed <$> boxed s a <*> boxed s b
        | otherwise -> pure False
  where
    args !i !j !n
      | n == 0 = pure True
      | otherwise = do
          x <- readCell s i
          y <- readCell s j
          ok <- equiv s x y
          if ok then args (i + 1) (j + 1) (n - 1) else pure False

-- | Groundness, memoised in the functor cell: a structure found ground is
-- marked, and the mark is trailed when a choice point could undo a binding
-- inside it.
isGroundWord :: Store -> Word' -> IO Bool
isGroundWord s w0 = do
  w <- deref s w0
  case tagOf w of
    t | t == tagRef -> pure False
      | t == tagStr -> do
          f <- readCell s (valOf w)
          if funGround f
            then pure True
            else do
              ok <- args (valOf w + 1) (funArity f)
              when ok $ do
                writeCell s (valOf w) (f .|. groundBit)
                trailValueIf s (valOf w) f
              pure ok
      | otherwise -> pure True
  where
    args !i !n
      | n == 0 = pure True
      | otherwise = do
          ok <- isGroundWord s =<< readCell s i
          if ok then args (i + 1) (n - 1) else pure False

-- | Does the unbound cell @addr@ occur in @w@?
occursIn :: Store -> Int -> Word' -> IO Bool
occursIn s addr w0 = do
  w <- deref s w0
  case tagOf w of
    t | t == tagRef -> pure (valOf w == addr)
      | t == tagStr -> do
          f <- readCell s (valOf w)
          if funGround f then pure False else args (valOf w + 1) (funArity f)
      | otherwise -> pure False
  where
    args !i !n
      | n == 0 = pure False
      | otherwise = do
          hit <- occursIn s addr =<< readCell s i
          if hit then pure True else args (i + 1) (n - 1)

-- | Build a term on the heap. Variables map through the supplied cell table;
-- unknown variables get fresh cells and extend the table.
importTerm :: Store -> IORef (IM.IntMap Int) -> Term -> IO Word'
importTerm s table term = do
  words' <- newIORef . IM.map refWord =<< readIORef table
  w <- importTermWords s words' term
  final <- readIORef words'
  writeIORef table (IM.map valOf final)
  pure w

-- | 'importTerm' with a table of arbitrary words for known variables.
importTermWords :: Store -> IORef (IM.IntMap Word') -> Term -> IO Word'
importTermWords s table term = case term of
  Var v -> do
    known <- readIORef table
    case IM.lookup v known of
      Just w -> pure w
      Nothing -> do
        addr <- allocCells s 1
        modifyIORef' table (IM.insert v (refWord addr))
        pure (refWord addr)
  Atom a -> atmWord <$> internAtom (symbols s) a
  IntLit n
    | fitsImmediate n -> pure (intWord (fromInteger n))
    | otherwise -> box s (BInt n)
  FloatLit d -> box s (BFlt d)
  CharLit c -> pure (chrWord (fromEnum c))
  StrLit str -> box s (BStr str)
  Compound f as -> do
    fid <- internFunctor (symbols s) f (length as)
    words' <- mapM (importTermWords s table) as
    structureWord s (funWord fid (length as)) words'

-- | Read a term back. Unbound cells already in @names@ keep that name.
-- With @stable@, any other cell is named by 'nameCell' and keeps the name;
-- without, it is numbered by first occurrence from @next@ for this export
-- only.
exportTermWith :: Store -> Bool -> IORef (IM.IntMap VarId) -> IORef VarId -> Word' -> IO Term
exportTermWith s stable names next w0 = do
  w <- deref s w0
  case tagOf w of
    t | t == tagRef -> do
          known <- readIORef names
          case IM.lookup (valOf w) known of
            Just v -> pure (Var v)
            Nothing -> do
              v <-
                if stable
                  then nameCell s (valOf w)
                  else do
                    v <- readIORef next
                    writeIORef next (v + 1)
                    pure v
              modifyIORef' names (IM.insert (valOf w) v)
              pure (Var v)
      | t == tagInt -> pure (IntLit (toInteger (valOf w)))
      | t == tagAtm -> Atom <$> atomName (symbols s) (valOf w)
      | t == tagChr -> pure (CharLit (toEnum (valOf w)))
      | t == tagBox -> do
          value <- boxed s w
          pure $ case value of
            BInt n -> IntLit n
            BFlt d -> FloatLit d
            BStr str -> StrLit str
      | t == tagStr -> do
          f <- readCell s (valOf w)
          (name, arity) <- functorName (symbols s) (funId f)
          as <- mapM (\i -> readCell s (valOf w + i) >>= exportTermWith s stable names next) [1 .. arity]
          pure (Compound name as)
      | otherwise -> fail "exportTerm: functor word outside a structure"

exportTerm :: Store -> Word' -> IO Term
exportTerm s w = do
  names <- newIORef IM.empty
  next <- newIORef 0
  exportTermWith s False names next w
