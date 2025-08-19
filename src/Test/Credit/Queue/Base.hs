{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, UndecidableInstances #-}

module Test.Credit.Queue.Base where

import Control.Monad.Credit
import Test.Credit
import Test.QuickCheck

data QueueOp a = Snoc a | Uncons
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (QueueOp a) where
  arbitrary = frequency
    [ (7, Snoc <$> arbitrary)
    , (3, pure Uncons)
    ]

class Queue q where
  empty :: MonadLazy m => m (q a m)
  snoc :: MonadInherit m => q a m -> a -> m (q a m)
  uncons :: MonadInherit m => q a m -> m (Maybe (a, q a m))

class Queue q => BoundedQueue q where
  qcost :: Size -> QueueOp a -> Credit

data Q q a m = Q (q (PrettyCell a) m)

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (Q q a) where
  prettyStructure (Q q) = prettyStructure q

instance (Arbitrary a, BoundedQueue q, Show a) => DataStructure (Q q a) (QueueOp a) where
  cost = qcost @q
  create = Q <$> empty
  perform sz (Q q) (Snoc x) = (sz + 1,) <$> Q <$> snoc q (PrettyCell x)
  perform sz (Q q) Uncons = do
    m <- uncons q
    q' <- case m of
      Nothing -> empty
      Just (_, q') -> pure q'
    pure (max 0 (sz - 1), Q q')