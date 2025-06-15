{-# LANGUAGE GADTs #-}

module Test.Credit.Deque.Streams (Stream(..), SLazyCon(..), smatch, credit, eval, c) where

import Prelude hiding (lookup, reverse)
import Control.Monad.Credit

c :: Int
c = 5

data Stream m a
  = SCons a (Stream m a)
  | SNil
  | SIndirect (SThunk m (Stream m a))

type SThunk m = Thunk m (SLazyCon m)

data SLazyCon m a where
  SAppend :: Stream m a -> Stream m a -> SLazyCon m (Stream m a)
  SRevDrop :: Int -> Stream m a -> Stream m a -> SLazyCon m (Stream m a)
  STake :: Int -> Stream m a -> SLazyCon m (Stream m a)

instance MonadInherit m => HasStep (SLazyCon m) m where
  step (SAppend xs ys) = sappend xs ys
  step (SRevDrop n xs ys) = srevdrop n xs ys
  step (STake n xs) = stake n xs

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
taildelay t = delay t >>= \x -> creditAllTo x >> pure (SIndirect x)

stake :: MonadInherit m => Int -> Stream m a -> m (Stream m a)
stake 0 xs = pure SNil
stake n xs = smatch xs
  (\x xs -> SCons x <$> taildelay (STake (n - 1) xs))
  (pure SNil)

srevdrop :: MonadInherit m => Int -> Stream m a -> Stream m a -> m (Stream m a)
srevdrop 0 xs ys = smatch xs
  (\x xs -> taildelay (SRevDrop 0 xs (SCons x ys)))
  (pure ys)
srevdrop n xs ys = smatch xs
  (\x xs -> taildelay (SRevDrop (n - 1) xs ys))
  (fail "drop: empty stream")

credit :: MonadInherit m => Credit -> Stream m a -> m ()
credit n (SIndirect i) = creditWith i n
credit _ _ = pure ()

evalone :: MonadInherit m => Stream m a -> m ()
evalone (SIndirect i) = force i >> pure ()
evalone _ = pure ()

eval :: MonadInherit m => Int -> Stream m a -> m ()
eval 0 s = pure ()
eval n s = evalone s >> eval (n - 1) s

sappend :: MonadInherit m => Stream m a -> Stream m a -> m (Stream m a)
sappend xs ys = credit (fromIntegral c) ys >> eval c ys >> smatch xs
  (\x xs -> SCons x <$> taildelay (SAppend xs ys))
  (pure ys)

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SLazyCon m a) where
  prettyCell (SAppend xs ys) = do
    xs' <- prettyCell xs
    ys' <- prettyCell ys
    pure $ mkMCell "SAppend" [xs', ys']
  prettyCell (SRevDrop n xs ys) = do
    n' <- prettyCell n
    xs' <- prettyCell xs
    ys' <- prettyCell ys
    pure $ mkMCell "SRevDrop" [n', xs', ys']
  prettyCell (STake n xs) = do
    n' <- prettyCell n
    xs' <- prettyCell xs
    pure $ mkMCell "STake" [n', xs']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Stream m a) where
  prettyCell xs = mkMList <$> toList xs <*> toHole xs
    where
      toList SNil = pure $ []
      toList (SCons x xs) = (:) <$> prettyCell x <*> toList xs
      toList (SIndirect t) = pure $ []

      toHole SNil = pure $ Nothing
      toHole (SCons x xs) = toHole xs
      toHole (SIndirect t) = Just <$> prettyCell t