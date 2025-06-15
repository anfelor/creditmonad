module Test.Credit.Heap.Pairing where

import Prettyprinter (Pretty)

import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

-- Binary pairing heaps as in Exercise 5.8 of Okasaki's book.

data PairingHeap a m
  = Nil
  | Heap a (PairingHeap a m) (PairingHeap a m)

-- | At the root, the right child is Empty.
data Pairing a m = Empty | Root a (PairingHeap a m)

link :: Ord a => Pairing a m -> Pairing a m -> Pairing a m
link Empty b = b
link a Empty = a
link (Root x a) (Root y b)
  | x <= y    = Root x (Heap y b a)
  | otherwise = Root y (Heap x a b)

mergePairs :: (MonadCredit m, Ord a) => PairingHeap a m -> m (Pairing a m)
mergePairs Nil = pure $ Empty
mergePairs (Heap x a1 Nil) = pure $ Root x a1
mergePairs (Heap x a1 (Heap y a2 a3)) = tick >> link ((link (Root x a1) (Root y a2))) <$> mergePairs a3

instance Heap Pairing where
  empty = pure Empty
  insert x h = merge (Root x Nil) h
  merge a b = tick >> pure (link a b)
  splitMin Empty = pure Nothing
  splitMin (Root x h) = Just . (x,) <$> mergePairs h

-- We can only prove a log(n) bound for insert, but this seems to work (as conjectured by Okasaki and others).
instance BoundedHeap Pairing where
  hcost n (Insert _) = 1
  hcost n Merge = 1
  hcost n SplitMin = 5 * log2 (n + 1)

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (PairingHeap a m) where
  prettyCell Nil = pure $ mkMCell "Nil" []
  prettyCell (Heap a l r) = do
    a' <- prettyCell a
    l' <- prettyCell l
    r' <- prettyCell r
    pure $ mkMCell "Heap" [a', l', r']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Pairing a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Root a l) = do
    a' <- prettyCell a
    l' <- prettyCell l
    pure $ mkMCell "Root" [a', l']

instance Pretty a => MemoryStructure (Pairing (PrettyCell a)) where
  prettyStructure = prettyCell