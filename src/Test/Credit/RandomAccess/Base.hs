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
  empty :: MonadLazy m => m (q a m)
  cons :: MonadCredit m => a -> q a m  -> m (q a m)
  uncons :: MonadCredit m => q a m -> m (Maybe (a, q a m))
  lookup :: MonadCredit m => Int -> q a m -> m (Maybe a)
  update :: MonadCredit m => Int -> a -> q a m -> m (q a m)

class RandomAccess q => BoundedRandomAccess q where
  qcost :: Size -> RandomAccessOp a -> Credit

data RA q a m = RA (q (PrettyCell a) m)

instance (MemoryCell m (q (PrettyCell a) m)) => MemoryCell m (RA q a m) where
  prettyCell (RA q) = prettyCell q

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (RA q a) where
  prettyStructure (RA q) = prettyStructure q

idx :: Int -> Size -> Int
idx i sz = if sz <= 0 then 0 else abs (i `mod` fromIntegral sz)

norm :: Size -> RandomAccessOp a -> RandomAccessOp a
norm sz (Lookup i) = Lookup (idx i sz)
norm sz (Update i a) = Update (idx i sz) a
norm _ op = op

instance (Arbitrary a, BoundedRandomAccess q, Show a) => DataStructure (RA q a) (RandomAccessOp a) where
  charge sz op = qcost @q sz (norm sz op)
  create = RA <$> empty
  action sz (RA q) (Cons x) = (sz + 1,) <$> RA <$> cons (PrettyCell x) q
  action sz (RA q) Uncons = do
    m <- uncons q
    m' <- case m of
      Nothing -> empty
      Just (_, q') -> pure q'
    pure (max 0 (sz - 1), RA m')
  action sz (RA q) (Lookup i) = do
    _ <- lookup (idx i sz) q
    pure $ (sz, RA q)
  action sz (RA q) (Update i a) = (sz,) <$> RA <$> update (idx i sz) (PrettyCell a) q