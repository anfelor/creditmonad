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
  empty :: MonadCredit m => m (q a m)
  add :: MonadCredit m => Ord a => a -> q a m -> m (q a m)
  sort :: MonadCredit m => Ord a => q a m -> m [a] 

class Sortable q => BoundedSortable q where
  scost :: Size -> SortableOp a -> Credit

data S q a m = E | S Size (q (PrettyCell a) m)

instance (MemoryCell m (q (PrettyCell a) m)) => MemoryCell m (S q a m) where
  prettyCell E = pure $ mkMCell "" []
  prettyCell (S _ q) = prettyCell q

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (S q a) where
  prettyStructure E = pure $ mkMCell "" []
  prettyStructure (S sz q) = prettyStructure q

act :: (MonadCredit m, Sortable q, Ord a) => Size -> q (PrettyCell a) m -> SortableOp a -> m (S q a m)
act sz q (Add x) = S (sz + 1) <$> add (PrettyCell x) q
act sz q Sort = do
  xs <- sort q
  pure $ S sz q

instance (Arbitrary a, Ord a, BoundedSortable q, Show a) => DataStructure (S q a) (SortableOp a) where
  create = E
  action E op = (scost @q 0 op, empty >>= flip (act 0) op)
  action (S sz q) op = (scost @q sz op, act sz q op)