module Test.Credit.Deque.Bankers where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Deque.Base
import Test.Credit.Deque.Streams

-- | Delay a computation, but do not consume any credits
indirect :: MonadInherit m => SLazyCon m (Stream m a) -> m (Stream m a)
indirect t = delay t >>= pure . SIndirect

data BDeque a m = BDeque
  { front :: Stream m a
  , lenf :: !Int
  , ghostf :: Stream m a
  , rear :: Stream m a
  , lenr :: !Int
  , ghostr :: Stream m a
  }

isEmpty :: BDeque a m -> Bool
isEmpty (BDeque _ 0 _ _ 0 _) = True
isEmpty (BDeque _ _ _ _ _ _) = False

size :: BDeque a m -> Int
size (BDeque _ lenf _ _ lenr _) = lenf + lenr

-- Rough proof sketch:
-- After rebalancing, the front and rear streams have at most lenf + lenr debits.
-- Need (c - 1) * n/2 cons operations before rebalance, which means we have to
-- pay off 2 / (c - 1) debits on each stream per cons operation.
-- Need (c - 1) / c * n/2 uncons operations before rebalance, which means we have to
-- pay off at least 2*c / (c - 1) debits on each stream per uncons operation
-- (but also at least (c + 1) debits to be able to force on element).
-- Not sure if the analysis above works for c < 3

bdeque :: MonadInherit m => BDeque a m -> m (BDeque a m)
bdeque (BDeque f lenf gf r lenr gr)
  | lenf > c * lenr + 1 = do
    let i = (lenf + lenr) `div` 2
    let j = lenf + lenr - i
    f' <- indirect (STake i f)
    f'' <- indirect (SRevDrop i f SNil)
    credit (fromIntegral c) f'' >> eval (fromIntegral c) f''
    r' <- indirect (SAppend r f'')
    credit 1 r'
    pure $ BDeque f' i f' r' j r'
  | lenr > c * lenf + 1 = do
    let j = (lenf + lenr) `div` 2
    let i = lenf + lenr - j
    r' <- indirect (STake j r)
    r'' <- indirect (SRevDrop j r SNil)
    credit (fromIntegral c) r'' >> eval (fromIntegral c) r''
    f' <- indirect (SAppend f r'')
    credit 1 f'
    pure $ BDeque f' i f' r' j r'
  | otherwise =
    pure $ BDeque f lenf gf r lenr gr

instance Deque BDeque where
  empty = pure $ BDeque SNil 0 SNil SNil 0 SNil
  cons x (BDeque f fl gf r rl gr) = credit 1 gf >> credit 1 gr >>
    bdeque (BDeque (SCons x f) (fl + 1) gf r rl gr)
  snoc (BDeque f fl gf r rl gr) x = credit 1 gf >> credit 1 gr >>
    bdeque (BDeque f fl gf (SCons x r) (rl + 1) gr)
  uncons (BDeque f fl gf r rl gr) = credit (fromIntegral c + 1) gf >> credit (fromIntegral c + 1) gr >> smatch f
    (\x f -> bdeque (BDeque f (fl - 1) gf r rl gr) >>= \q -> pure $ Just (x, q))
    (smatch r
      (\x _ -> empty >>= \q -> pure $ Just (x, q))
      (pure Nothing))
  unsnoc (BDeque f fl gf r rl gr) = credit (fromIntegral c + 1) gr >> credit (fromIntegral c + 1) gf >> smatch r
    (\x r -> bdeque (BDeque f fl gf r (rl - 1) gr) >>= \q -> pure $ Just (q, x))
    (smatch f
      (\x _ -> empty >>= \q -> pure $ Just (q, x))
      (pure Nothing))
  concat = undefined

instance BoundedDeque BDeque where
  qcost _ (Cons _) = fromIntegral c + 3
  qcost _ (Snoc _) = fromIntegral c + 3
  qcost _ Uncons = 3 * fromIntegral c + 4
  qcost _ Unsnoc = 3 * fromIntegral c + 4
  qcost _ Concat = 0

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (BDeque a m) where
  prettyCell (BDeque f fl _ r rl _) = do
    f' <- prettyCell f
    fl' <- prettyCell fl
    r' <- prettyCell r
    rl' <- prettyCell rl
    pure $ mkMCell "BDeque" [f', fl', r', rl']

instance Pretty a => MemoryStructure (BDeque (PrettyCell a)) where
  prettyStructure = prettyCell