module Test.Credit.Deque.Realtime where

import Prelude hiding (lookup, reverse)

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit.Deque.Base
import Test.Credit.Deque.Streams

-- | Delay a computation, but do not consume any credits
indirect :: MonadInherit m => SLazyCon m (Stream m a) -> m (Stream m a)
indirect t = delay t >>= pure . SIndirect

data RDeque a m = RDeque
  { lenf :: !Int
  , front :: Stream m a
  , sf :: Stream m a
  , lenr :: !Int
  , rear :: Stream m a
  , sr :: Stream m a
  }

exec1 :: MonadInherit m => Stream m a -> m (Stream m a)
exec1 xs = credit (fromIntegral c + 1) xs >> smatch xs
  (\_ xs -> pure xs)
  (pure SNil)

exec2 :: MonadInherit m => Stream m a -> m (Stream m a)
exec2 xs = exec1 xs >>= exec1

rdeque :: MonadInherit m => RDeque a m -> m (RDeque a m)
rdeque (RDeque lenf f sf lenr r sr)
  | lenf > c * lenr + 1 = do
    let i = (lenf + lenr) `div` 2
    let j = lenf + lenr - i
    f' <- indirect (STake i f)
    f'' <- indirect (SRevDrop i f SNil)
    r' <- indirect (SAppend r f'')
    credit (fromIntegral c) f'' >> eval (fromIntegral c) f''
    pure $ RDeque i f' f' j r' r'
  | lenr > c * lenf + 1 = do
    let j = (lenf + lenr) `div` 2
    let i = lenf + lenr - j
    r' <- indirect (STake j r)
    r'' <- indirect (SRevDrop j r SNil)
    f' <- indirect (SAppend f r'')
    credit (fromIntegral c) r'' >> eval (fromIntegral c) r''
    pure $ RDeque i f' f' j r' r'
  | otherwise =
    pure $ RDeque lenf f sf lenr r sr

instance Deque RDeque where
  empty = pure $ RDeque 0 SNil SNil 0 SNil SNil
  cons x (RDeque lenf f sf lenr r sr) = exec1 sf >>= \sf -> exec1 sr >>= \sr ->
    rdeque (RDeque (lenf + 1) (SCons x f) sf lenr r sr)
  snoc (RDeque lenf f sf lenr r sr) x = exec1 sf >>= \sf -> exec1 sr >>= \sr ->
    rdeque (RDeque lenf f sf (lenr + 1) (SCons x r) sr)
  uncons (RDeque lenf f sf lenr r sr) = exec2 sf >>= \sf -> exec2 sr >>= \sr -> smatch f
    (\x f -> rdeque (RDeque (lenf - 1) f sf lenr r sr) >>= \q -> pure $ Just (x, q))
    (pure Nothing)
  unsnoc (RDeque lenf f sf lenr r sr) = exec2 sf >>= \sf -> exec2 sr >>= \sr -> smatch r
    (\x r -> rdeque (RDeque lenf f sf (lenr - 1) r sr) >>= \q -> pure $ Just (q, x))
    (pure Nothing)
  concat = undefined

instance BoundedDeque RDeque where
  qcost _ (Cons _) = 3 * fromIntegral c + 4
  qcost _ (Snoc _) = 3 * fromIntegral c + 4
  qcost _ Uncons = 5 * fromIntegral c + 8
  qcost _ Unsnoc = 5 * fromIntegral c + 8
  qcost _ Concat = 0

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (RDeque a m) where
  prettyCell (RDeque lenf f sf lenr r sr) = do
    lenf' <- prettyCell lenf
    f' <- prettyCell f
    sf' <- prettyCell sf
    lenr' <- prettyCell lenr
    r' <- prettyCell r
    sr' <- prettyCell sr
    pure $ mkMCell "Deque" [lenf', f', sf', lenr', r', sr']

instance Pretty a => MemoryStructure (RDeque (PrettyCell a)) where
  prettyStructure = prettyCell