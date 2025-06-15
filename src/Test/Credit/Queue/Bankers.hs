module Test.Credit.Queue.Bankers where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Queue.Base
import Test.Credit.Queue.Streams

data BQueue a m = BQueue
  { front :: Stream m a
  , flen :: !Int
  , rear :: Stream m a
  , rlen :: !Int
  }

bqueue :: MonadInherit m => BQueue a m -> m (BQueue a m)
bqueue (BQueue f fl r rl) = do
  ifIndirect f (`hasAtLeast` fromIntegral rl)
  if fl >= rl 
    then pure $ BQueue f fl r rl
    else do
      r' <- delay (SReverse r SNil)
      r' `creditWith` 1
      f' <- delay (SAppend f (SIndirect r'))
      pure $ BQueue (SIndirect f') (fl + rl) SNil 0

instance Queue BQueue where
  empty = pure $ BQueue SNil 0 SNil 0
  snoc (BQueue f fl r rl) x = do
    credit f
    bqueue (BQueue f fl (SCons x r) (rl + 1))
  uncons (BQueue f fl r rl) = do
    credit f >> credit f
    smatch f
      (\x f -> do
        q <- bqueue (BQueue f (fl - 1) r rl)
        pure $ Just (x, q))
      (pure Nothing)

isEmpty :: BQueue a m -> Bool
isEmpty (BQueue _ flen _ rlen) = flen == 0 && rlen == 0

lazyqueue :: MonadInherit m => BQueue a m -> m [a]
lazyqueue (BQueue f fl r rl) = do
  f' <- toList f
  r' <- toList r
  pure $ f' ++ reverse r'

instance BoundedQueue BQueue where
  qcost _ (Snoc _) = 2
  qcost _ Uncons = 4

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (BQueue a m) where
  prettyCell (BQueue f fl r rl) = do
    f' <- prettyCell f
    fl' <- prettyCell fl
    r' <- prettyCell r
    rl' <- prettyCell rl
    pure $ mkMCell "Queue" [f', fl', r', rl']

instance Pretty a => MemoryStructure (BQueue (PrettyCell a)) where
  prettyStructure = prettyCell