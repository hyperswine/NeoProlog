{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | The core resolution store: one growable unboxed array of tagged words,
-- a trail of addresses, a boxed-constant table and interned symbol tables.
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
    resetSlots, resetFrame, markerWord, logicalId,
    replaceLogicalIds, collectionStats, recordCollection,
    readArg, writeArg, saveArgs, loadArgs, reserveCells, groundNowWord,
    readReg, writeReg, rVAL, rGCLIM, rCLP, rBOUND, initialCollectLimit, markerBase, markerVars,
    drainBound, recordBoundCell,
    deref, bind, unwindTrail, trailIf, trailValueIf,
    structureWord, structure2, structure2WithGround,
    box, boxed,
    -- * Unification and equality
    unify, equiv, isGroundWord, occursIn,
    -- * Term exchange
    importTerm, importTermWords, exportTerm, exportTermWith,
  )
where

import Control.Monad (when)
import Data.Array.Base (getNumElements, unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, IOUArray, newArray, newArray_)
import Data.Bits (complement, shiftL, shiftR, (.&.), (.|.))
import Data.IORef
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
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

-- | Atom and functor tables. Compilation interns everything a program and
-- query mention; builtins intern the rare constant they create at runtime.
data Symbols = Symbols
  { atomIds :: !(IORef (Map.Map String Int)),
    atomNames :: !(IORef (IM.IntMap String)),
    functorIds :: !(IORef (Map.Map (String, Int) Int)),
    functorNames :: !(IORef (IM.IntMap (String, Int)))
  }

newSymbols :: IO Symbols
newSymbols = Symbols <$> newIORef Map.empty <*> newIORef IM.empty <*> newIORef Map.empty <*> newIORef IM.empty

internAtom :: Symbols -> String -> IO Int
internAtom symbols name = do
  ids <- readIORef (atomIds symbols)
  case Map.lookup name ids of
    Just i -> pure i
    Nothing -> do
      let i = Map.size ids
      writeIORef (atomIds symbols) (Map.insert name i ids)
      modifyIORef' (atomNames symbols) (IM.insert i name)
      pure i

internFunctor :: Symbols -> String -> Int -> IO Int
internFunctor symbols name arity = do
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

-- Register slots of the unboxed register file.
rH, rTR, rHB, rOUT, rBOX, rARITH, rFRESH, rCAP, rVAL :: Int
rH = 0
rTR = 1
rHB = 2
rOUT = 3
rBOX = 4
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

initialCollectLimit :: Int
initialCollectLimit = 262144

readReg :: Store -> Int -> IO Int
readReg s = unsafeRead (regs s)
{-# INLINE readReg #-}

writeReg :: Store -> Int -> Int -> IO ()
writeReg s = unsafeWrite (regs s)
{-# INLINE writeReg #-}

data Store = Store
  { cells :: !(IORef (IOUArray Int Int)),
    trail :: !(IORef (IOUArray Int Int)),
    boxes :: !(IORef (IOArray Int Boxed)),
    regs :: !(IOUArray Int Int),
    -- | argument registers of the call being made
    argRegs :: !(IOUArray Int Int),
    -- | cells bound since the last reconciliation with the constraint store
    bound :: !(IORef (IOUArray Int Int)),
    -- | Exact logical identities of the live activation slots detached by
    -- collection. Fresh activations still use their compact block marker.
    logicalIds :: !(IORef (IM.IntMap Int)),
    symbols :: !Symbols
  }

-- Cells are never read before they are written, so the array need not be
-- initialised; untouched pages cost nothing.
initialCells :: Int
initialCells = 1048576

newStore :: Symbols -> IO Store
newStore syms = do
  cs <- newArray_ (0, initialCells - 1)
  tr <- newArray (0, 4095) 0
  bx <- newArray_ (0, 255)
  rs <- newArray (0, 15) 0
  unsafeWrite rs rCAP initialCells
  unsafeWrite rs rGCLIM initialCollectLimit
  ar <- newArray (0, 4095) 0
  bd <- newArray (0, 255) 0
  Store <$> newIORef cs <*> newIORef tr <*> newIORef bx <*> pure rs <*> pure ar <*> newIORef bd <*> newIORef IM.empty <*> pure syms

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
  arr <- readIORef (cells s)
  let go !i
        | i >= n = pure ()
        | otherwise = unsafeRead (argRegs s) i >>= unsafeWrite arr (top + i) >> go (i + 1)
  go 0
  unsafeWrite (regs s) rH (top + n)
  pure top

loadArgs :: Store -> Int -> Int -> IO ()
loadArgs s addr n = do
  arr <- readIORef (cells s)
  let go !i
        | i >= n = pure ()
        | otherwise = unsafeRead arr (addr + i) >>= unsafeWrite (argRegs s) i >> go (i + 1)
  go 0

heapTop, trailTop, hb, outLen, arithData, freshId :: Store -> IO Int
heapTop s = unsafeRead (regs s) rH
trailTop s = unsafeRead (regs s) rTR
hb s = unsafeRead (regs s) rHB
outLen s = unsafeRead (regs s) rOUT
arithData s = unsafeRead (regs s) rARITH
-- | The reference engine's next fresh variable id along this branch.
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
  arr <- readIORef (cells s)
  unsafeRead arr i
{-# INLINE readCell #-}

writeCell :: Store -> Int -> Word' -> IO ()
writeCell s i w = do
  arr <- readIORef (cells s)
  unsafeWrite arr i w
{-# INLINE writeCell #-}

ensureCells :: Store -> Int -> IO ()
ensureCells s needed = do
  capacity <- unsafeRead (regs s) rCAP
  when (needed > capacity) (growCells s needed)
{-# INLINE ensureCells #-}

growCells :: Store -> Int -> IO ()
growCells s needed = do
  arr <- readIORef (cells s)
  size <- getNumElements arr
  let size' = max needed (size * 4)
  arr' <- newArray_ (0, size' - 1)
  top <- heapTop s
  let copy !i
        | i >= top = pure ()
        | otherwise = unsafeRead arr i >>= unsafeWrite arr' i >> copy (i + 1)
  copy 0
  writeIORef (cells s) arr'
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
  arr <- readIORef (cells s)
  let go !i
        | i >= top + n = pure ()
        | otherwise = unsafeWrite arr i (refWord i) >> go (i + 1)
  go top
  unsafeWrite (regs s) rH (top + n)
  pure top

-- | A marker cell precedes every block of activation variables. Functor
-- words never occur as values, so a marker is unambiguous when scanning
-- down from a variable cell. Its value is the reference engine's id of the
-- first variable of the block, which keeps exported variable names equal.
-- The marker packs the block size above bit 40 so collection can retain
-- each surviving slot's logical identity independently of its frame.
markerWord :: Int -> Int -> Word'
markerWord logicalBase n = mkWord tagFun (logicalBase .|. (n `shiftL` 40))
{-# INLINE markerWord #-}

markerBase :: Word' -> Int
markerBase w = valOf w .&. (2 ^ (40 :: Int) - 1)

markerVars :: Word' -> Int
markerVars w = valOf w `shiftR` 40

-- | Reserve @n@ variable cells preceded by a marker; returns the address of
-- the first variable.
allocSlots :: Store -> Int -> Int -> IO Int
allocSlots s logicalBase n = do
  top <- heapTop s
  ensureCells s (top + n + 1)
  arr <- readIORef (cells s)
  unsafeWrite arr top (markerWord logicalBase n)
  let go !i
        | i > top + n = pure ()
        | otherwise = unsafeWrite arr i (refWord i) >> go (i + 1)
  go (top + 1)
  -- Allocation only grows the suffix; sparse identities need pruning
  -- solely when a rollback or collection lowers the heap top.
  unsafeWrite (regs s) rH (top + n + 1)
  pure (top + 1)
{-# INLINE allocSlots #-}

-- | Allocate a clause activation, clearing only the supplied variable
-- offsets. Every omitted slot must be written by its first head occurrence
-- before a matcher or head constructor reads it. The compiled layout is
-- shared across calls; stable logical-variable allocations use 'allocSlots'.
allocFrame :: Store -> Int -> Int -> [Int] -> IO Int
allocFrame s logicalBase count initialize = do
  top <- heapTop s
  ensureCells s (top + count + 1)
  arr <- readIORef (cells s)
  unsafeWrite arr top (markerWord logicalBase count)
  let base = top + 1
      go [] = pure ()
      go (offset : offsets) = do
        let addr = base + offset
        unsafeWrite arr addr (refWord addr)
        go offsets
  go initialize
  unsafeWrite (regs s) rH (top + count + 1)
  pure base
{-# INLINE allocFrame #-}

-- | Read an activation operand without exposing its storage cell. A value
-- already installed in the slot can be shared directly; a still-unbound
-- local must first acquire a stable logical-variable cell outside the
-- reusable activation. Promotion preserves the reference engine's fresh
-- identity and does not consume another fresh id. Redirecting the operand
-- is an ordinary binding, so an older choice restores its self-reference
-- before reclaiming the promoted cell.
--
-- Query cells and captured 'PWord' operands are logical variables already:
-- callers pass only the addresses of live activation operands here.
operandWord :: Store -> Int -> IO Word'
operandWord s addr = do
  value <- readCell s addr >>= deref s
  if value == refWord addr
    then do
      ident <- maybe addr id <$> logicalId s addr
      stable <- allocSlots s ident 1
      let word = refWord stable
      bind s addr word
      pure word
    else pure value
{-# INLINE operandWord #-}

-- | The operand accessor for a fresh contiguous activation. Its marker
-- gives a local's logical identity directly, avoiding a backward scan when
-- an unbound operand is promoted. Captured plans detached by collection use
-- ready words instead, and must never call this function with a dummy base.
operandAt :: Store -> Int -> Int -> IO Word'
operandAt s base offset = do
  let addr = base + offset
  -- Non-self references were installed from already stable operands. They
  -- can be passed on as references: eagerly dereferencing here adds a walk
  -- that the consuming matcher/builtin would otherwise perform once.
  value <- readCell s addr
  if value == refWord addr
    then do
      marker <- readCell s (base - 1)
      stable <- allocSlots s (markerBase marker + offset) 1
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
--
-- The uncommon compacted-block case discards the old sparse identities and
-- exposes this marker to identity lookup again. Ordinary repeated tail
-- calls stay in the fresh suffix and avoid traversing the identity map.
resetSlots :: Store -> Int -> Int -> Int -> IO ()
resetSlots s logicalBase base capacity = resetFrame s logicalBase base capacity [0 .. capacity - 1]
{-# INLINE resetSlots #-}

-- | Reset an unreachable tail activation with a compiled initialization
-- layout. The reachability and choice-boundary requirements of 'resetSlots'
-- apply. Omitted offsets must be initialized by first head occurrences before
-- they are read, exactly as for 'allocFrame'.
resetFrame :: Store -> Int -> Int -> Int -> [Int] -> IO ()
resetFrame s logicalBase base capacity initialize = do
  ids <- readIORef (logicalIds s)
  case IM.lookupGE base ids of
    Just (addr, _) | addr < base + capacity ->
      let (before, _, remaining) = IM.splitLookup base ids
          (_, _, after) = IM.splitLookup (base + capacity - 1) remaining
       in writeIORef (logicalIds s) (IM.union before after)
    _ -> pure ()
  boundary <- unsafeRead (regs s) rIDENT
  when (base < boundary) (unsafeWrite (regs s) rIDENT (base - 1))
  arr <- readIORef (cells s)
  unsafeWrite arr (base - 1) (markerWord logicalBase capacity)
  let go [] = pure ()
      go (offset : offsets) = do
        let addr = base + offset
        unsafeWrite arr addr (refWord addr)
        go offsets
  go initialize
{-# INLINE resetFrame #-}

-- | The reference id of a variable cell: sparse identity after collection,
-- otherwise the marker of a fresh activation block.
logicalId :: Store -> Int -> IO (Maybe Int)
logicalId s addr = do
  ids <- readIORef (logicalIds s)
  case IM.lookup addr ids of
    Just ident -> pure (Just ident)
    Nothing -> do
      -- Older compacted cells have no marker. Restrict the scan to the
      -- freshly allocated suffix, whose blocks still have their markers.
      boundary <- unsafeRead (regs s) rIDENT
      arr <- readIORef (cells s)
      let go !i
            | i < boundary = pure Nothing
            | otherwise = do
                w <- unsafeRead arr i
                if tagOf w == tagFun
                  then pure $ if addr <= i + markerVars w
                    then Just (markerBase w + addr - i - 1)
                    else Nothing
                  else go (i - 1)
      go (addr - 1)

-- Register 12 bounds the prefix whose activation markers have been
-- replaced by sparse identities; the remaining registers are GC counters.
rIDENT, rGCCOUNT, rGCLIVE, rGCRECLAIM :: Int
rIDENT = 12
rGCCOUNT = 13
rGCLIVE = 14
rGCRECLAIM = 15

-- | Install identities while collection's original addresses are still
-- available. The compacted prefix ends at the supplied heap top.
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
  arr <- readIORef (cells s)
  unsafeWrite arr addr (if ground then functor .|. groundBit else functor)
  let fill !_ [] = pure ()
      fill !i (w : ws) = unsafeWrite arr i w >> fill (i + 1) ws
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
  arr <- readIORef (cells s)
  unsafeWrite arr addr (if ground then functor .|. groundBit else functor)
  unsafeWrite arr (addr + 1) a
  unsafeWrite arr (addr + 2) b
  pure (strWord addr)
{-# INLINE structure2WithGround #-}

-- | Follow reference chains. The result is either a non-REF word or the
-- REF of an unbound cell.
deref :: Store -> Word' -> IO Word'
deref s !w
  | tagOf w == tagRef = do
      arr <- readIORef (cells s)
      let go !v = do
            v' <- unsafeRead arr (valOf v)
            if v' == v || tagOf v' /= tagRef then pure v' else go v'
      go w
  | otherwise = pure w
{-# INLINE deref #-}

-- Trail entries: an even entry @2*addr@ resets the cell to unbound; an odd
-- entry @2*addr+1@ restores the word pushed just below it.
pushTrail :: Store -> Int -> IO ()
pushTrail s entry = do
  tr <- readIORef (trail s)
  top <- trailTop s
  size <- getNumElements tr
  tr' <-
    if top < size
      then pure tr
      else do
        grown <- newArray (0, size * 2 - 1) 0
        let copy !i
              | i >= top = pure ()
              | otherwise = unsafeRead tr i >>= unsafeWrite grown i >> copy (i + 1)
        copy 0
        writeIORef (trail s) grown
        pure grown
  unsafeWrite tr' top entry
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
  arr <- readIORef (bound s)
  top <- unsafeRead (regs s) rBOUND
  size <- getNumElements arr
  arr' <-
    if top < size
      then pure arr
      else do
        grown <- newArray (0, size * 2 - 1) 0
        let copy !i
              | i >= top = pure ()
              | otherwise = unsafeRead arr i >>= unsafeWrite grown i >> copy (i + 1)
        copy 0
        writeIORef (bound s) grown
        pure grown
  unsafeWrite arr' top addr
  unsafeWrite (regs s) rBOUND (top + 1)

-- | Take the recorded bindings, oldest first, and clear the record.
drainBound :: Store -> IO [Int]
drainBound s = do
  top <- unsafeRead (regs s) rBOUND
  arr <- readIORef (bound s)
  addrs <- mapM (unsafeRead arr) [0 .. top - 1]
  unsafeWrite (regs s) rBOUND 0
  pure addrs

-- | Reset every trailed cell above @mark@ to unbound and restore the mark.
unwindTrail :: Store -> Int -> IO ()
unwindTrail s mark = do
  tr <- readIORef (trail s)
  top <- trailTop s
  arr <- readIORef (cells s)
  let go !i
        | i < mark = pure ()
        | otherwise = do
            entry <- unsafeRead tr i
            if even entry
              then do
                let addr = entry `shiftR` 1
                unsafeWrite arr addr (refWord addr)
                go (i - 1)
              else do
                old <- unsafeRead tr (i - 1)
                unsafeWrite arr (entry `shiftR` 1) old
                go (i - 2)
  go (top - 1)
  setTrailTop s mark

box :: Store -> Boxed -> IO Word'
box s value = do
  bx <- readIORef (boxes s)
  top <- unsafeRead (regs s) rBOX
  size <- getNumElements bx
  bx' <-
    if top < size
      then pure bx
      else do
        grown <- newArray_ (0, size * 2 - 1)
        let copy !i
              | i >= top = pure ()
              | otherwise = unsafeRead bx i >>= unsafeWrite grown i >> copy (i + 1)
        copy 0
        writeIORef (boxes s) grown
        pure grown
  unsafeWrite bx' top value
  unsafeWrite (regs s) rBOX (top + 1)
  pure (boxWord top)

boxed :: Store -> Word' -> IO Boxed
boxed s w = do
  bx <- readIORef (boxes s)
  unsafeRead bx (valOf w)
{-# INLINE boxed #-}

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
            -- Promotion and tail-frame reuse decouple physical addresses
            -- from logical age. Keep the reference engine's smaller fresh
            -- id as representative, with addresses as a tie-breaker for
            -- cells that have no marker identity.
            let aa = valOf a
                ba = valOf b
            ai <- maybe aa id <$> logicalId s aa
            bi <- maybe ba id <$> logicalId s ba
            if (ai, aa) > (bi, ba)
              then bind s aa b >> pure True
              else bind s ba a >> pure True
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

-- | Read a term back. Unbound cells take the id their activation marker
-- gives them; cells without a marker are named by first occurrence from
-- @next@.
exportTermWith :: Store -> IORef (IM.IntMap VarId) -> IORef VarId -> Word' -> IO Term
exportTermWith s names next w0 = do
  w <- deref s w0
  case tagOf w of
    t | t == tagRef -> do
          known <- readIORef names
          case IM.lookup (valOf w) known of
            Just v -> pure (Var v)
            Nothing -> do
              marked <- logicalId s (valOf w)
              v <- case marked of
                Just v -> pure v
                Nothing -> do
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
          as <- mapM (\i -> readCell s (valOf w + i) >>= exportTermWith s names next) [1 .. arity]
          pure (Compound name as)
      | otherwise -> fail "exportTerm: functor word outside a structure"

exportTerm :: Store -> Word' -> IO Term
exportTerm s w = do
  names <- newIORef IM.empty
  next <- newIORef 0
  exportTermWith s names next w
