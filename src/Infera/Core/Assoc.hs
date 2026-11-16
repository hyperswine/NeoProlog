{-# LANGUAGE BangPatterns #-}
-- | Heap-native execution of the verified std AVL predicates. Only searched
-- keys and inspected heights need to be immediate integers. Values and
-- untouched branches retain their original words and variable identities.
-- Unsupported shapes return Nothing without binding anything, so the caller
-- can run the original clauses, including their errors and relational modes.
module Infera.Core.Assoc (nativeAssoc) where

import Control.Monad (guard)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT (..), runMaybeT)
import Infera.Core.Store

nativeAssoc :: Store -> Bool -> [Word'] -> IO (Maybe (Maybe Word'))
nativeAssoc store insert arguments = do
  empty <- atmWord <$> internAtom (symbols store) "empty"
  node <- (\fid -> funWord fid 5) <$> internFunctor (symbols store) "node" 5
  let immediate word = do
        value <- lift (deref store word)
        guard (tagOf value == tagInt)
        pure (valOf value)
      fields word = do
        value <- lift (deref store word)
        guard (tagOf value == tagStr)
        functor <- lift (readCell store (valOf value))
        guard (funKey functor == node)
        let at i = lift (readCell store (valOf value+i))
        (,,,) <$> at 1 <*> at 2 <*> at 4 <*> at 5
      height word = do
        value <- lift (deref store word)
        if value == empty then pure 0 else do
          guard (tagOf value == tagStr)
          functor <- lift (readCell store (valOf value))
          guard (funKey functor == node)
          lift (readCell store (valOf value+3)) >>= immediate
      make key value left right = do
        lh <- height left
        rh <- height right
        let h = toInteger (max lh rh)+1
        guard (fitsImmediate h)
        lift (structureWord store node [key,value,intWord (fromInteger h),left,right])
      balance key value left right = do
        lh <- height left
        rh <- height right
        if lh-rh > 1 then do
          (lk,lv,ll,lr) <- fields left
          llh <- height ll
          lrh <- height lr
          if llh >= lrh then do
            r <- make key value lr right
            make lk lv ll r
          else do
            (mk,mv,ml,mr) <- fields lr
            l <- make lk lv ll ml
            r <- make key value mr right
            make mk mv l r
        else if lh-rh < -1 then do
          (rk,rv,rl,rr) <- fields right
          rlh <- height rl
          rrh <- height rr
          if rrh >= rlh then do
            l <- make key value left rl
            make rk rv l rr
          else do
            (mk,mv,ml,mr) <- fields rl
            l <- make key value left ml
            r <- make rk rv mr rr
            make mk mv l r
        else make key value left right
      get !depth !key tree = do
        guard (depth < (256::Int))
        value <- lift (deref store tree)
        if value == empty then pure Nothing else do
          (k,v,left,right) <- fields value
          at <- immediate k
          case compare key at of
            EQ -> pure (Just v)
            LT -> get (depth+1) key left
            GT -> get (depth+1) key right
      put !depth !key keyWord tree newValue = do
        guard (depth < (256::Int))
        value <- lift (deref store tree)
        if value == empty
          then lift (structureWord store node [keyWord,newValue,intWord 1,empty,empty])
          else do
            (k,v,left,right) <- fields value
            at <- immediate k
            case compare key at of
              EQ -> make k newValue left right
              LT -> do child <- put (depth+1) key keyWord left newValue; balance k v child right
              GT -> do child <- put (depth+1) key keyWord right newValue; balance k v left child
  runMaybeT $ case (insert,arguments) of
    (False,[key,tree,_]) -> immediate key >>= \k -> get 0 k tree
    (True,[key,tree,value,_]) -> do
      k <- immediate key
      Just <$> put 0 k (intWord k) tree value
    _ -> MaybeT (pure Nothing)
