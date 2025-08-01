{-# LANGUAGE AllowAmbiguousTypes, TypeApplications #-}

module Test.Credit.Deque.Base (DequeOp(..), Deque(..), BoundedDeque(..), D, BD) where

import Prelude hiding (concat)
import Control.Monad.Credit
import Test.Credit
import Test.QuickCheck

data DequeOp a = Cons a | Snoc a | Uncons | Unsnoc | Concat
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (DequeOp a) where
  arbitrary = frequency
    [ (7, Cons <$> arbitrary)
    , (4, Snoc <$> arbitrary)
    , (2, pure Uncons)
    , (6, pure Unsnoc)
    , (1, pure Concat)
    ]

class Deque q where
  empty :: MonadLazy m => m (q a m)
  cons :: MonadInherit m => a -> q a m -> m (q a m)
  snoc :: MonadInherit m => q a m -> a -> m (q a m)
  uncons :: MonadInherit m => q a m -> m (Maybe (a, q a m))
  unsnoc :: MonadInherit m => q a m -> m (Maybe (q a m, a))
  concat :: MonadInherit m => q a m -> q a m -> m (q a m)

class Deque q => BoundedDeque q where
  qcost :: Size -> DequeOp a -> Credit

data D q a m = D (q (PrettyCell a) m)

instance (MemoryCell m (q (PrettyCell a) m)) => MemoryCell m (D q a m) where
  prettyCell (D q) = prettyCell q

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (D q a) where
  prettyStructure (D q) = prettyStructure q


instance (Arbitrary a, BoundedDeque q, Show a) => DataStructure (D q a) (DequeOp a) where
  charge _ Concat = 0
  charge sz op = qcost @q sz op
  create = D <$> empty
  action sz (D q) (Cons x) = (sz + 1,) <$> D <$> cons (PrettyCell x) q
  action sz (D q) (Snoc x) = (sz + 1,) <$> D <$> snoc q (PrettyCell x)
  action sz (D q) Uncons = do
    m <- uncons q
    case m of
      Nothing -> (sz,) <$> D <$> empty
      Just (_, q') -> pure (sz - 1, D q')
  action sz (D q) Unsnoc = do
    m <- unsnoc q
    case m of
      Nothing -> (sz,) <$> D <$> empty
      Just (q', _) -> pure (sz - 1, D q')
  action sz (D q) Concat = pure $ (sz, D q) -- no op

data BD q a m = BD (D q a m) (D q a m)

instance (MemoryCell m (q (PrettyCell a) m)) => MemoryCell m (BD q a m) where
  prettyCell (BD q1 q2) = do
    q1' <- prettyCell q1
    q2' <- prettyCell q2
    pure $ mkMCell "Concat" [q1', q2']

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (BD q a) where
  prettyStructure (BD q1 q2) = do
    q1' <- prettyStructure q1
    q2' <- prettyStructure q2
    pure $ mkMCell "Concat" [q1', q2']

instance (Arbitrary a, BoundedDeque q, Show a) => DataStructure (BD q a) (DequeOp a) where
  charge = qcost @q
  create = do
    q1 <- empty
    q2 <- empty
    pure $ BD (D q1) (D q2)
  action sz (BD q1 q2) (Cons x) = do
    (sz, q1) <- action sz q1 (Cons x)
    pure (sz, BD q1 q2)
  action sz (BD q1 q2) (Snoc x) = do
    (sz, q2) <- action sz q2 (Snoc x)
    pure (sz, BD q1 q2)
  action sz (BD q1 q2) Uncons = do
    (sz, q1) <- action sz q1 Uncons
    pure (sz, BD q1 q2)
  action sz (BD q1 q2) Unsnoc = do
    (sz, q2) <- action sz q2 Unsnoc
    pure (sz, BD q1 q2)
  action sz (BD (D q1) (D q2)) Concat = do
    e <- empty
    q <- concat q1 q2
    pure (sz, BD (D e) (D q))