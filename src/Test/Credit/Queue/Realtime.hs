{-# LANGUAGE LambdaCase #-}

module Test.Credit.Queue.Realtime where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit.Queue.Base
import Test.Credit.Queue.Streams

data RQueue a m = RQueue
  { front :: Stream m a
  , rear :: Stream m a
  , schedule :: Stream m a
  }

rqueue :: MonadInherit m => RQueue a m -> m (RQueue a m)
rqueue (RQueue f r s) = do
  s `creditWith` 2
  force s >>= \case
    SCons _ s -> pure $ RQueue f r s
    SNil -> do
      r' <- sreverse r =<< nil
      f' <- sappend f r'
      r' `creditWith` 1
      n <- nil
      pure $ RQueue f' n f'

instance Queue RQueue where
  empty = do
    n <- nil
    pure $ RQueue n n n
  snoc (RQueue f r s) x = do
    r' <- cons x r
    rqueue $ RQueue f r' s
  uncons (RQueue f r s) = do
    f `creditWith` 2
    force f >>= \case
      SCons x f -> do
        q <- rqueue $ RQueue f r s
        pure $ Just (x, q)
      SNil -> pure Nothing

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