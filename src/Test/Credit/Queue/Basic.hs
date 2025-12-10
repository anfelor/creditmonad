{-# LANGUAGE LambdaCase, GADTs #-}

module Test.Credit.Queue.Basic where

import Control.Monad.Credit
import Data.Maybe (fromMaybe)
import Prettyprinter (Pretty)
import Test.Credit
import Test.Credit.Queue.Base
import qualified Test.Credit.Queue.Bankers as B

newtype BasicQueue a m = BasicQueue (B.BQueue a m)

instance Queue BasicQueue where
  empty = BasicQueue <$> empty
  snoc (BasicQueue q) x = BasicQueue <$> snoc q x
  uncons (BasicQueue q) = do
    m <- uncons q
    pure $ fmap (\(x, q') -> (x, BasicQueue q')) m

isEmpty :: BasicQueue a m -> Bool
isEmpty (BasicQueue q) = B.isEmpty q

size :: BasicQueue a m -> Int
size (BasicQueue q) = B.size q

lazyqueue :: MonadLazy m => BasicQueue a m -> m [a]
lazyqueue (BasicQueue q) = B.lazyqueue q

instance BoundedQueue BasicQueue where
  qcost n op = qcost @B.BQueue n op

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (BasicQueue a m) where
  prettyCell (BasicQueue q) = do
    xs <- mapM prettyCell =<< B.lazyqueue q
    pure $ mkMList xs Nothing

instance Pretty a => MemoryStructure (BasicQueue (PrettyCell a)) where
  prettyStructure = prettyCell