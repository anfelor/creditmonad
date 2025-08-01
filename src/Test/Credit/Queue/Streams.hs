{-# LANGUAGE GADTs, LambdaCase #-}

module Test.Credit.Queue.Streams (Stream, StreamCell(..), SLazyCon(..), cons, nil, sappend, sreverse, slength, toList, test) where

import Control.Monad
import Control.Monad.Credit

type Stream m a = Thunk m (SLazyCon m) (StreamCell m a)

data StreamCell m a
  = SCons a (Stream m a)
  | SNil

data SLazyCon m a where
  SAppend :: Stream m a -> Stream m a -> SLazyCon m (StreamCell m a)
  SReverse :: Stream m a -> Stream m a -> SLazyCon m (StreamCell m a)

instance MonadInherit m => HasStep (SLazyCon m) m where
  step (SAppend xs ys) = force =<< sappend' xs ys 
  step (SReverse xs ys) = force =<< sreverse' xs ys

cons :: MonadLazy m => a -> Stream m a -> m (Stream m a)
cons x xs = value $ SCons x xs

nil :: MonadLazy m => m (Stream m a)
nil = value SNil

-- | delay a computation, consuming all credits
taildelay :: MonadInherit m => SLazyCon m (StreamCell m a) -> m (Stream m a)
taildelay t = do
  x <- delay t
  creditAllTo x
  pure x

sreverse :: MonadInherit m => Stream m a -> Stream m a -> m (Stream m a)
sreverse xs ys = delay $ SReverse xs ys

sreverse' :: MonadInherit m => Stream m a -> Stream m a -> m (Stream m a)
sreverse' xs ys = tick >> force xs >>= \case
  SCons x xs -> do
    xys <- value $ SCons x ys
    sreverse' xs xys
  SNil -> pure ys

sappend :: MonadInherit m => Stream m a -> Stream m a -> m (Stream m a)
sappend xs ys = delay $ SAppend xs ys

sappend' :: MonadInherit m => Stream m a -> Stream m a -> m (Stream m a)
sappend' xs ys = tick >> creditWith ys 1 >> force xs >>= \case
  SCons x xs -> value . SCons x =<< taildelay (SAppend xs ys)
  SNil -> creditAllTo ys >> pure ys

cellToList :: MonadLazy m => StreamCell m a -> m [a]
cellToList SNil = pure []
cellToList (SCons x xs) = (x :) <$> toList xs

toList :: MonadLazy m => Stream m a -> m [a]
toList t = do
  lazymatch t cellToList $ \case
      SAppend xs ys -> do
        xs' <- toList xs
        ys' <- toList ys
        pure $ xs' ++ ys'
      SReverse xs ys -> do
        xs' <- toList xs
        ys' <- toList ys
        pure $ reverse xs' ++ ys'

slength :: MonadLazy m => Stream m a -> m Int
slength s = length <$> toList s

walk :: MonadInherit m => Stream m a -> m ()
walk s = force s >>= \case
  SCons _ xs -> walk xs
  SNil -> pure ()

foo :: MonadInherit m => Stream m a -> m ()
foo s = void $ force s

test :: MonadInherit m => m ()
test = do
  nil <- value SNil
  one <- value (SCons 1 nil)
  two <- value (SCons 2 nil)
  s <- sappend one two
  creditWith s 2
  foo s
  creditWith s 1
  walk s

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SLazyCon m a) where
  prettyCell (SAppend xs ys) = do
    xs' <- prettyCell xs
    ys' <- prettyCell ys
    pure $ mkMCell "SAppend" [xs', ys']
  prettyCell (SReverse xs ys) = do
    xs' <- prettyCell xs
    ys' <- prettyCell ys
    pure $ mkMCell "SReverse" [xs', ys']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (StreamCell m a) where
  prettyCell xs = mkMList <$> toList xs <*> toHole xs
    where
      toList SNil = pure $ []
      toList (SCons x xs) = (:) <$> prettyCell x <*> lazymatch xs toList (\_ -> pure [])

      toHole SNil = pure $ Nothing
      toHole (SCons x xs) = lazymatch xs toHole (\_ -> Just <$> prettyCell xs)