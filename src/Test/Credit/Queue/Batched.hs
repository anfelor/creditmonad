module Test.Credit.Queue.Batched where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Queue.Base

data Batched a m = Batched [a] [a]

rev :: MonadCount m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc)

bqueue :: MonadCount m => Batched a m -> m (Batched a m)
bqueue (Batched [] rear) = rev rear [] >>= \f -> pure $ Batched f []
bqueue (Batched front rear) = pure $ Batched front rear

instance Queue Batched where
  empty = pure $ Batched [] []
  snoc (Batched front rear) x = bqueue (Batched front (x : rear))
  uncons (Batched [] rear) = pure Nothing
  uncons (Batched (x:front) rear) = Just . (x,) <$> bqueue (Batched front rear)

instance BoundedQueue Batched where
  qcost n (Snoc _) = 1
  qcost n Uncons = linear n

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Batched a m) where
  prettyCell (Batched f r) = do
    f' <- prettyCell f
    r' <- prettyCell r
    pure $ mkMCell "Queue" [f', r']

instance Pretty a => MemoryStructure (Batched (PrettyCell a)) where
  prettyStructure = prettyCell