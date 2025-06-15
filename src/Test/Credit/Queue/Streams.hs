{-# LANGUAGE GADTs, LambdaCase #-}

module Test.Credit.Queue.Streams (Stream(..), SThunk, SLazyCon(..), smatch, credit, evalone, toList, ifIndirect, test) where

import Control.Monad
import Control.Monad.Credit

data Stream m a
  = SCons a (Stream m a)
  | SNil
  | SIndirect (SThunk m (Stream m a))

type SThunk m = Thunk m (SLazyCon m)

data SLazyCon m a where
  SAppend :: Stream m a -> Stream m a -> SLazyCon m (Stream m a)
  SReverse :: Stream m a -> Stream m a -> SLazyCon m (Stream m a)

instance MonadInherit m => HasStep (SLazyCon m) m where
  step (SAppend xs ys) = sappend xs ys
  step (SReverse xs ys) = sreverse xs ys

-- | Smart destructor for streams, consuming one credit
smatch :: MonadInherit m => Stream m a -- ^ Scrutinee
       -> (a -> Stream m a -> m b) -- ^ Cons case
       -> m b -- ^ Nil case
       -> m b
smatch x cons nil = tick >> eval x
  where
    eval x = case x of
      SCons a as -> cons a as
      SNil -> nil
      SIndirect i -> force i >>= eval

-- | delay a computation, consuming all credits
taildelay :: MonadInherit m => SLazyCon m (Stream m a) -> m (Stream m a)
taildelay t = do
  x <- delay t
  creditAllTo x
  pure (SIndirect x)

sreverse :: MonadInherit m => Stream m a -> Stream m a -> m (Stream m a)
sreverse xs ys = smatch xs
  (\x xs -> taildelay (SReverse xs (SCons x ys)))
  (pure ys)

ifIndirect :: Monad m => Stream m a -> (SThunk m (Stream m a) -> m ()) -> m ()
ifIndirect (SIndirect i) f = f i
ifIndirect _ _ = pure ()

credit :: MonadInherit m => Stream m a -> m ()
credit s = ifIndirect s (`creditWith` 1)

evalone :: MonadInherit m => Stream m a -> m ()
evalone s = ifIndirect s (void . force)

sappend :: MonadInherit m => Stream m a -> Stream m a -> m (Stream m a)
sappend xs ys = credit ys >> evalone ys >> smatch xs
  (\x xs -> SCons x <$> taildelay (SAppend xs ys))
  (pure ys)

walk s = smatch s (\_ xs -> walk xs) (pure ())

foo :: MonadInherit m => Stream m a -> m ()
foo s = smatch s (\_ _ -> pure ()) (pure ())

test :: MonadInherit m => m ()
test = do
  s <- sappend (SCons 1 SNil) (SCons 2 SNil)
  credit s >> credit s
  foo s
  credit s
  walk s

toList :: MonadLazy m => Stream m a -> m [a]
toList SNil = pure []
toList (SCons x xs) = do
  xs' <- toList xs
  pure $ x : xs'
toList (SIndirect t) = do
  lazymatch t toList $ \case
      SAppend xs ys -> do
        xs' <- toList xs
        ys' <- toList ys
        pure $ xs' ++ ys'
      SReverse xs ys -> do
        xs' <- toList xs
        ys' <- toList ys
        pure $ reverse xs' ++ ys'

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SLazyCon m a) where
  prettyCell (SAppend xs ys) = do
    xs' <- prettyCell xs
    ys' <- prettyCell ys
    pure $ mkMCell "SAppend" [xs', ys']
  prettyCell (SReverse xs ys) = do
    xs' <- prettyCell xs
    ys' <- prettyCell ys
    pure $ mkMCell "SReverse" [xs', ys']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Stream m a) where
  prettyCell xs = mkMList <$> toList xs <*> toHole xs
    where
      toList SNil = pure $ []
      toList (SCons x xs) = (:) <$> prettyCell x <*> toList xs
      toList (SIndirect t) = pure $ []

      toHole SNil = pure $ Nothing
      toHole (SCons x xs) = toHole xs
      toHole (SIndirect t) = Just <$> prettyCell t