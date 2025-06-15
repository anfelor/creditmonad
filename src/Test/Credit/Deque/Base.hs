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
  empty :: MonadInherit m => m (q a m)
  cons :: MonadInherit m => a -> q a m -> m (q a m)
  snoc :: MonadInherit m => q a m -> a -> m (q a m)
  uncons :: MonadInherit m => q a m -> m (Maybe (a, q a m))
  unsnoc :: MonadInherit m => q a m -> m (Maybe (q a m, a))
  concat :: MonadInherit m => q a m -> q a m -> m (q a m)

class Deque q => BoundedDeque q where
  qcost :: Size -> DequeOp a -> Credit

data D q a m = E | D Size (q (PrettyCell a) m)

instance (MemoryCell m (q (PrettyCell a) m)) => MemoryCell m (D q a m) where
  prettyCell E = pure $ mkMCell "" []
  prettyCell (D _ q) = prettyCell q

instance (MemoryStructure (q (PrettyCell a))) => MemoryStructure (D q a) where
  prettyStructure E = pure $ mkMCell "" []
  prettyStructure (D _ q) = prettyStructure q

act :: (MonadInherit m, Deque q) => Size -> q (PrettyCell a) m -> DequeOp a -> m (D q a m)
act sz q (Cons x) = D (sz + 1) <$> cons (PrettyCell x) q
act sz q (Snoc x) = D (sz + 1) <$> snoc q (PrettyCell x)
act sz q Uncons = do
  m <- uncons q
  case m of
    Nothing -> pure E
    Just (_, q') -> pure $ D (max 0 (sz - 1)) q'
act sz q Unsnoc = do
  m <- unsnoc q
  case m of
    Nothing -> pure E
    Just (q', _) -> pure $ D (max 0 (sz - 1)) q'
act sz q Concat = pure $ D sz q

instance (Arbitrary a, BoundedDeque q, Show a) => DataStructure (D q a) (DequeOp a) where
  create = E
  action E op = (qcost @q 0 op, empty >>= flip (act 0) op)
  action (D sz q) op = (qcost @q sz op, act sz q op)

size :: D q a m -> Size
size E = 0
size (D sz _) = sz

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

act1 :: (MonadInherit m, Deque q) => DequeOp a -> BD q a m -> m (BD q a m)
act1 op (BD q1 q2) = do
  q1' <- case q1 of
    E -> empty
    D _ q -> pure q
  q1'' <- act (size q1) q1' op 
  pure $ BD q1'' q2

act2 :: (MonadInherit m, Deque q) => DequeOp a -> BD q a m -> m (BD q a m)
act2 op (BD q1 q2) = do
  let sz = size q2
  q2' <- case q2 of
    E -> empty
    D _ q -> pure q
  q2'' <- act (size q2) q2' op 
  pure $ BD q1 q2''

concatenate :: (MonadInherit m, Deque q) => D q a m -> D q a m -> m (D q a m)
concatenate E E = pure E
concatenate (D sz1 q1) E = pure $ D sz1 q1
concatenate E (D sz2 q2) = pure $ D sz2 q2
concatenate (D sz1 q1) (D sz2 q2) = D (sz1 + sz2) <$> concat q1 q2

instance (Arbitrary a, BoundedDeque q, Show a) => DataStructure (BD q a) (DequeOp a) where
  create = BD E E
  action (BD q1 q2) (Cons x) = (qcost @q (size q1) (Cons x), act1 (Cons x) (BD q1 q2))
  action (BD q1 q2) (Snoc x) = (qcost @q (size q2) (Snoc x), act2 (Snoc x) (BD q1 q2))
  action (BD q1 q2) Uncons = (qcost @q (size q1) Uncons, act1 Uncons (BD q1 q2))
  action (BD q1 q2) Unsnoc = (qcost @q (size q2) Unsnoc, act2 Unsnoc (BD q1 q2))
  action (BD q1 q2) Concat = (qcost @q (size q1 + size q2) Concat, BD E <$> concatenate q1 q2)