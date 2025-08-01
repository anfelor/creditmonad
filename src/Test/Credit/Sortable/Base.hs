{-# LANGUAGE AllowAmbiguousTypes, TypeApplications #-}

module Test.Credit.Sortable.Base where

import Control.Monad.Credit
import Test.Credit
import Test.QuickCheck

data SortableOp a = Add a | Sort
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (SortableOp a) where
  arbitrary = frequency
    [ (9, Add <$> arbitrary)
    , (1, pure Sort)
    ]

class Sortable q where
  empty :: MonadLazy m => m (q a m)
  add :: MonadCredit m => Ord a => a -> q a m -> m (q a m)
  sort :: MonadCredit m => Ord a => q a m -> m [a] 

class Sortable q => BoundedSortable q where
  scost :: Size -> SortableOp a -> Credit

data S q a m = S (q (PrettyCell a) m)

instance (MemoryCell m (q (PrettyCell a) m)) => MemoryCell m (S q a m) where
  prettyCell (S q) = prettyCell q

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (S q a) where
  prettyStructure (S q) = prettyStructure q

instance (Arbitrary a, Ord a, BoundedSortable q, Show a) => DataStructure (S q a) (SortableOp a) where
  charge = scost @q
  create = S <$> empty
  action sz (S q) (Add x) = (sz + 1,) <$> S <$> add (PrettyCell x) q
  action sz (S q) Sort = do
    _ <- sort q
    pure (sz, S q)