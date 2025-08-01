{-# LANGUAGE LambdaCase, GADTs #-}

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

bqueue :: MonadInherit m => m (Stream m a) -> Int -> m (Stream m a) -> Int -> m (BQueue a m)
bqueue f fl r rl = (\f r -> BQueue f fl r rl) <$> f <*> r

allEvaluated :: MonadInherit m => StreamCell m a -> m ()
allEvaluated SNil = pure ()
allEvaluated (SCons _ xs) = isEvaluated xs

isEvaluated :: MonadInherit m => Stream m a -> m ()
isEvaluated s = lazymatch s allEvaluated (error "Stream should be pure")

invariant :: MonadInherit m => Stream m a -> Int -> m ()
invariant front rlen = 
  lazymatch front (\_ -> pure ()) $ \case
    SAppend xs ys -> do
      lxs <- slength xs
      lys <- slength ys
      front `hasAtLeast` (fromIntegral $ min rlen (2 * lxs))
      invariant xs lxs
      ys `hasAtLeast` (fromIntegral $ lys - lxs)
    SReverse xs ys -> do
      isEvaluated xs
      isEvaluated ys

restructure :: MonadInherit m => BQueue a m -> m (BQueue a m)
restructure (BQueue f fl r rl) = do
  invariant f $ fromIntegral rl
  if fl >= rl 
    then do
      pure $ BQueue f fl r rl
    else do
      r' <- sreverse r =<< nil
      r' `creditWith` 1
      bqueue (sappend f r') (fl + rl) nil 0

instance Queue BQueue where
  empty = (\f r -> BQueue f 0 r 0) <$> nil <*> nil
  snoc (BQueue f fl r rl) x = do
    f `creditWith` 1
    restructure =<< bqueue (pure f) fl (cons x r) (rl + 1)
  uncons (BQueue f fl r rl) = do
    f `creditWith` 2
    force f >>= \case
      SCons x f -> do
        q <- restructure $ BQueue f (fl - 1) r rl
        pure $ Just (x, q)
      SNil -> pure Nothing

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