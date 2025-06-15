{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, UndecidableInstances #-}

module Test.Credit.Queue.Base where

import Control.Monad.Credit
import Prettyprinter
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
  empty :: MonadInherit m => m (q a m)
  snoc :: MonadInherit m => q a m -> a -> m (q a m)
  uncons :: MonadInherit m => q a m -> m (Maybe (a, q a m))

class Queue q => BoundedQueue q where
  qcost :: Size -> QueueOp a -> Credit

data Q q a m = E | Q Size (q (PrettyCell a) m)

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (Q q a) where
  prettyStructure E = pure $ mkMCell "" []
  prettyStructure (Q _ q) = prettyStructure q

act :: (MonadInherit m, Queue q) => Size -> q (PrettyCell a) m -> QueueOp a -> m (Q q a m)
act sz q (Snoc x) = Q (sz + 1) <$> snoc q (PrettyCell x)
act sz q Uncons = do
  m <- uncons q
  case m of
    Nothing -> pure E
    Just (_, q') -> pure $ Q (max 0 (sz - 1)) q'

instance (Arbitrary a, BoundedQueue q, Show a) => DataStructure (Q q a) (QueueOp a) where
  create = E
  action E op = (qcost @q 0 op, empty >>= flip (act 0) op)
  action (Q sz q) op = (qcost @q sz op, act sz q op)