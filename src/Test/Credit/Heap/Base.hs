{-# LANGUAGE AllowAmbiguousTypes, TypeApplications #-}

module Test.Credit.Heap.Base (HeapOp(..), Heap(..), BoundedHeap(..), H, BH) where

import Control.Monad.Credit
import Test.Credit
import Test.QuickCheck

data HeapOp a = Insert a | Merge | SplitMin
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (HeapOp a) where
  arbitrary = frequency
    [ (6, Insert <$> arbitrary)
    , (3, pure SplitMin)
    , (1, pure Merge)
    ]

class Heap h where
  empty :: MonadLazy m => m (h a m)
  insert :: MonadCredit m => Ord a => a -> h a m -> m (h a m)
  merge :: MonadCredit m => Ord a => h a m -> h a m -> m (h a m)
  splitMin :: MonadCredit m => Ord a => h a m -> m (Maybe (a, h a m))

class Heap h => BoundedHeap h where
  hcost :: Size -> HeapOp a -> Credit

data H h a m = H (h (PrettyCell a) m)

instance (MemoryCell m (h (PrettyCell a) m)) => MemoryCell m (H h a m) where
  prettyCell (H h) = prettyCell h

instance (MemoryStructure (h (PrettyCell a))) => MemoryStructure (H h a) where
  prettyStructure (H h) = prettyStructure h

instance (Arbitrary a, Ord a, BoundedHeap h, Show a) => DataStructure (H h a) (HeapOp a) where
  charge sz Merge = 0
  charge sz op = hcost @h sz op
  create = H <$> empty
  action sz (H h) (Insert x) = (sz + 1,) <$> H <$> insert (PrettyCell x) h
  action sz (H h) Merge = pure (sz, H h) -- no op
  action sz (H h) SplitMin = do
    m <- splitMin h
    case m of
      Nothing -> (sz,) <$> H <$> empty
      Just (_, h') -> pure (sz - 1, H h')

data BH h a m = BH (H h a m) (H h a m)

instance (MemoryCell m (h (PrettyCell a) m)) => MemoryCell m (BH h a m) where
  prettyCell (BH h1 h2) = do
    h1' <- prettyCell h1
    h2' <- prettyCell h2
    pure $ mkMCell "Merge" [h1', h2']

instance (MemoryStructure (h (PrettyCell a))) => MemoryStructure (BH h a) where
  prettyStructure (BH h1 h2) = do
    h1' <- prettyStructure h1
    h2' <- prettyStructure h2
    pure $ mkMCell "Merge" [h1', h2']

instance (Arbitrary a, Ord a, BoundedHeap h, Show a) => DataStructure (BH h a) (HeapOp a) where
  charge = hcost @h
  create = do
    h1 <- empty
    h2 <- empty
    pure $ BH (H h1) (H h2)
  action sz (BH h1 h2) (Insert a) = do
    (sz, h1) <- action sz h1 (Insert a)
    pure (sz, BH h1 h2)
  action sz (BH h1 h2) SplitMin = do
    (sz, h2) <- action sz h2 SplitMin
    pure (sz, BH h1 h2)
  action sz (BH (H h1) (H h2)) Merge = do
    h <- merge h1 h2
    e <- empty
    pure (sz, BH (H e) (H h))