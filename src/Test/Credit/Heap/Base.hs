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
  empty :: MonadCredit m => m (h a m)
  insert :: MonadCredit m => Ord a => a -> h a m -> m (h a m)
  merge :: MonadCredit m => Ord a => h a m -> h a m -> m (h a m)
  splitMin :: MonadCredit m => Ord a => h a m -> m (Maybe (a, h a m))

class Heap h => BoundedHeap h where
  hcost :: Size -> HeapOp a -> Credit

data H h a m = E | H Size (h (PrettyCell a) m)

instance (MemoryCell m (h (PrettyCell a) m)) => MemoryCell m (H h a m) where
  prettyCell E = pure $ mkMCell "" []
  prettyCell (H _ h) = prettyCell h

instance (MemoryStructure (h (PrettyCell a))) => MemoryStructure (H h a) where
  prettyStructure E = pure $ mkMCell "" []
  prettyStructure (H _ h) = prettyStructure h

act :: (MonadCredit m, Heap h, Ord a) => Size -> h (PrettyCell a) m -> HeapOp a -> m (H h a m)
act sz h (Insert x) = H (sz + 1) <$> insert (PrettyCell x) h
act sz h Merge = pure $ H sz h
act sz h SplitMin = do
  m <- splitMin h
  case m of
    Nothing -> pure E
    Just (_, h') -> pure $ H (max 0 (sz - 1)) h'

instance (Arbitrary a, Ord a, BoundedHeap h, Show a) => DataStructure (H h a) (HeapOp a) where
  create = E
  action E op = (hcost @h 0 op, empty >>= flip (act 0) op)
  action (H sz h) op = (hcost @h sz op, act sz h op)

size :: H h a m -> Size
size E = 0
size (H sz _) = sz

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

act1 :: (MonadInherit m, Heap h, Ord a) => HeapOp a -> BH h a m -> m (BH h a m)
act1 op (BH h1 h2) = do
  h1' <- case h1 of
    E -> empty
    H _ h -> pure h
  h1'' <- act (size h1) h1' op 
  pure $ BH h1'' h2

act2 :: (MonadInherit m, Heap h, Ord a) => HeapOp a -> BH h a m -> m (BH h a m)
act2 op (BH h1 h2) = do
  h2' <- case h2 of
    E -> empty
    H _ h -> pure h
  h2'' <- act (size h2) h2' op 
  pure $ BH h1 h2''

mergeH :: (MonadInherit m, Heap h, Ord a) => H h a m -> H h a m -> m (H h a m)
mergeH E E = pure E
mergeH (H sz1 h1) E = pure $ H sz1 h1
mergeH E (H sz2 h2) = pure $ H sz2 h2
mergeH (H sz1 h1) (H sz2 h2) = H (sz1 + sz2) <$> merge h1 h2

instance (Arbitrary a, Ord a, BoundedHeap h, Show a) => DataStructure (BH h a) (HeapOp a) where
  create = BH E E
  action (BH h1 h2) (Insert a) = (hcost @h (size h1) (Insert a),      act1 (Insert a) (BH h1 h2))
  action (BH h1 h2) SplitMin   = (hcost @h (size h2) SplitMin,        act2 SplitMin (BH h1 h2))
  action (BH h1 h2) Merge      = (hcost @h (size h1 + size h2) Merge, BH E <$> mergeH h1 h2)