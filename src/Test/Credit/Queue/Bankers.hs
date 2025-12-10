{-# LANGUAGE LambdaCase, GADTs #-}

module Test.Credit.Queue.Bankers where

import Control.Monad.Credit
import Data.Maybe (fromMaybe)
import Prettyprinter (Pretty)
import Test.Credit
import Test.Credit.Queue.Base
import Test.Credit.Queue.Streams

data BQueue a m = BQueue
  { flen :: !Int
  , rlen :: !Int
  , front :: Stream m a
  , rear  :: Stream m a
  }

allEvaluated :: MonadInherit m => StreamCell m a -> m ()
allEvaluated SNil = pure ()
allEvaluated (SCons _ xs) = isEvaluated xs

isEvaluated :: MonadInherit m => Stream m a -> m ()
isEvaluated s = lazymatch s allEvaluated (error "Stream should be pure")

allInvariant :: MonadInherit m => Maybe Int -> StreamCell m a -> m ()
allInvariant _ SNil = pure ()
allInvariant rlen (SCons x xs) = invariant xs (fmap (subtract 2) rlen)

invariant :: MonadInherit m => Stream m a -> Maybe Int -> m ()
invariant front rlen = 
  lazymatch front (allInvariant rlen) $ \case
    SAppend xs ys -> do
      lxs <- slength xs
      lys <- slength ys
      front `hasAtLeast` (fromIntegral $ fromMaybe (2 * lxs) rlen)
      invariant xs Nothing
      ys `hasAtLeast` (fromIntegral $ lys - lxs)
    SReverse xs ys -> do
      lxs <- slength xs
      front `hasAtLeast` (fromIntegral lxs)
      isEvaluated xs
      isEvaluated ys

bqueue :: MonadInherit m => Int -> Int -> Stream m a -> Stream m a -> m (BQueue a m)
bqueue fl rl f r = do
  isEvaluated r
  invariant f (Just rl)
  if fl >= rl 
    then pure $ BQueue fl rl f r
    else do
      r' <- delay . SReverse r =<< nil
      r' `creditWith` 1
      BQueue (fl + rl) 0 <$> (delay $ SAppend f r') <*> nil

instance Queue BQueue where
  empty = BQueue 0 0 <$> nil <*> nil
  snoc (BQueue fl rl f r) x = do
    f `creditWith` 1
    bqueue fl (rl + 1) f =<< cons x r
  uncons (BQueue fl rl f r) = do
    f `creditWith` 2
    force f >>= \case
      SCons x f' -> do
        q <- bqueue (fl - 1) rl f' r
        pure $ Just (x, q)
      SNil -> pure Nothing

isEmpty :: BQueue a m -> Bool
isEmpty (BQueue flen rlen _ _) = flen == 0 && rlen == 0

size :: BQueue a m -> Int
size (BQueue flen rlen _ _) = flen + rlen

lazyqueue :: MonadLazy m => BQueue a m -> m [a]
lazyqueue (BQueue fl rl f r) = do
  f' <- toList f
  r' <- toList r
  pure $ f' ++ reverse r'

instance BoundedQueue BQueue where
  qcost _ (Snoc _) = 2
  qcost _ Uncons = 4

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (BQueue a m) where
  prettyCell (BQueue fl rl f r) = do
    fl' <- prettyCell fl
    rl' <- prettyCell rl
    f' <- prettyCell f
    r' <- prettyCell r
    pure $ mkMCell "Queue" [fl', rl', f', r']

instance Pretty a => MemoryStructure (BQueue (PrettyCell a)) where
  prettyStructure = prettyCell