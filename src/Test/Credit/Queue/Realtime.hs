module Test.Credit.Queue.Realtime where

import Prelude hiding (lookup, reverse)

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit.Queue.Base
import Test.Credit.Queue.Streams

-- | Delay a computation, but do not consume any credits
indirect :: MonadInherit m => SLazyCon m (Stream m a) -> m (Stream m a)
indirect t = delay t >>= pure . SIndirect

data RQueue a m = RQueue
  { front :: Stream m a
  , rear :: Stream m a
  , schedule :: Stream m a
  }

rqueue :: MonadInherit m => RQueue a m -> m (RQueue a m)
rqueue (RQueue f r s) = credit s >> credit s >> smatch s
  (\x s -> pure $ RQueue f r s)
  (do
    r' <- indirect (SReverse r SNil)
    f' <- indirect (SAppend f r')
    credit r' >> evalone r'
    pure $ RQueue f' SNil f')

instance Queue RQueue where
  empty = pure $ RQueue SNil SNil SNil
  snoc (RQueue f r s) x = rqueue (RQueue f (SCons x r) s)
  uncons (RQueue f r s) = credit f >> credit f >> smatch f
    (\x f -> rqueue (RQueue f r s) >>= \q -> pure $ Just (x, q))
    (pure Nothing)

instance BoundedQueue RQueue where
  qcost _ (Snoc _) = 4
  qcost _ Uncons = 7

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (RQueue a m) where
  prettyCell (RQueue f r s) = do
    f' <- prettyCell f
    r' <- prettyCell r
    s' <- prettyCell s
    pure $ mkMCell "Queue" [f', r', s']

instance Pretty a => MemoryStructure (RQueue (PrettyCell a)) where
  prettyStructure = prettyCell