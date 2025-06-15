{-# LANGUAGE AllowAmbiguousTypes, TypeApplications #-}

module Test.Credit.RandomAccess.Base where

import Prelude hiding (lookup)
import Control.Monad.Credit
import Test.Credit
import Test.QuickCheck

data RandomAccessOp a = Cons a | Uncons | Lookup Int | Update Int a
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (RandomAccessOp a) where
  arbitrary = frequency
    [ (13, Cons <$> arbitrary)
    , (6, pure Uncons)
    , (1, Lookup <$> arbitrary)
    , (1, Update <$> arbitrary <*> arbitrary)
    ]

class RandomAccess q where
  empty :: MonadCredit m => m (q a m)
  cons :: MonadCredit m => a -> q a m  -> m (q a m)
  uncons :: MonadCredit m => q a m -> m (Maybe (a, q a m))
  lookup :: MonadCredit m => Int -> q a m -> m (Maybe a)
  update :: MonadCredit m => Int -> a -> q a m -> m (q a m)

class RandomAccess q => BoundedRandomAccess q where
  qcost :: Size -> RandomAccessOp a -> Credit

data RA q a m = E | RA Size (q (PrettyCell a) m)

instance (MemoryCell m (q (PrettyCell a) m)) => MemoryCell m (RA q a m) where
  prettyCell E = pure $ mkMCell "" []
  prettyCell (RA _ q) = prettyCell q

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (RA q a) where
  prettyStructure E = pure $ mkMCell "" []
  prettyStructure (RA _ q) = prettyStructure q

idx :: Int -> Size -> Int
idx i sz = if sz <= 0 then 0 else abs (i `mod` fromIntegral sz)

norm :: Size -> RandomAccessOp a -> RandomAccessOp a
norm sz (Lookup i) = Lookup (idx i sz)
norm sz (Update i a) = Update (idx i sz) a
norm _ op = op

act :: (MonadCredit m, RandomAccess q) => Size -> q (PrettyCell a) m -> RandomAccessOp a -> m (RA q a m)
act sz q (Cons x) = RA (sz + 1) <$> cons (PrettyCell x) q
act sz q Uncons = do
  m <- uncons q
  case m of
    Nothing -> pure E
    Just (_, q') -> pure $ RA (max 0 (sz - 1)) q'
act sz q (Lookup i) = do
  _ <- lookup i q
  pure $ RA sz q
act sz q (Update i a) = RA sz <$> update i (PrettyCell a) q

instance (Arbitrary a, BoundedRandomAccess q, Show a) => DataStructure (RA q a) (RandomAccessOp a) where
  create = E
  action E op = (qcost @q 0 (norm 0 op), empty >>= flip (act 0) (norm 0 op))
  action (RA sz q) op = (qcost @q sz (norm sz op), act sz q (norm sz op))