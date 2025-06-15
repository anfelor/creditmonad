{-# LANGUAGE TypeFamilies, StandaloneDeriving, UndecidableInstances, OverloadedStrings, DerivingStrategies, MagicHash #-}

module Control.Monad.Credit.CounterM (CounterM, runCounterM, CounterT, runCounterT) where

import Prelude hiding (lookup)
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State.Lazy
import Control.Monad.ST.Trans

import Control.Monad.Credit.Base

-- Run computation in a state monad

-- State of the computation
-- credits: The total credits consumed so far
newtype St = St Ticks
  deriving (Eq, Ord, Show)

-- | An instance of the counter monad using ST to memoize thunks.
type CounterM s = CounterT s Identity

-- | A monad transformer on the counter monad.
-- Warning! This monad transformer includes the ST monad transformer and
-- should not be used with monads that can contain multiple answers,
-- like the list monad. Safe monads include the monads State, Reader, Writer,
-- Maybe and combinations of their corresponding monad transformers.
newtype CounterT s m a = CounterT { runT :: StateT St (ExceptT String (STT s m)) a }

instance Functor m => Functor (CounterT s m) where
  fmap f (CounterT m) = CounterT (fmap f m)

instance Monad m => Applicative (CounterT s m) where
  pure = CounterT . pure
  CounterT f <*> CounterT x = CounterT (f <*> x)

instance Monad m => Monad (CounterT s m) where
  CounterT m >>= f = CounterT (m >>= runT . f)

instance Monad m => MonadError String (CounterT s m) where
  throwError e = CounterT (throwError e)
  catchError (CounterT m) h = CounterT (catchError m (runT . h))

instance Monad m => MonadState St (CounterT s m) where
  get = CounterT get
  put s = CounterT (put s)

instance MonadTrans (CounterT s) where
  lift = CounterT . lift . lift . lift

liftST :: Monad m => STT s m a -> CounterT s m a
liftST = CounterT . lift . lift

instance Monad m => MonadFail (CounterT s m) where
  fail e = throwError e

instance Monad m => MonadCount (CounterT s m) where
  tick = do
    (St c) <- get
    put (St (c + 1))

instance Monad m => MonadLazy (CounterT s m) where
  {-# SPECIALIZE instance MonadLazy (CounterT s Identity) #-}
  {-# SPECIALIZE instance MonadLazy (CounterT s (State st)) #-}
  data Thunk (CounterT s m) t b = Thunk !(STRef s (Either (t b) b))
  delay a = do
    s <- liftST $ newSTRef (Left a)
    pure (Thunk s)
  force (Thunk t) = do
    t' <- liftST $ readSTRef t
    case t' of
      Left a -> do
        b <- step a
        liftST $ writeSTRef t (Right b)
        pure b
      Right b -> pure b
  lazymatch (Thunk t) f g = do
    t' <- liftST $ readSTRef t
    case t' of
      Right b -> f b
      Left a -> g a

instance Monad m => MonadCredit (CounterT s m) where
  {-# SPECIALIZE instance MonadCredit (CounterT s Identity) #-}
  {-# SPECIALIZE instance MonadCredit (CounterT s (State st)) #-}
  creditWith _ _ = pure ()
  hasAtLeast _ _ = pure ()

instance Monad m => MonadInherit (CounterT s m) where
  {-# SPECIALIZE instance MonadInherit (CounterT s Identity) #-}
  {-# SPECIALIZE instance MonadInherit (CounterT s (State st)) #-}
  creditAllTo _ = pure ()

runStateT' :: Monad m => StateT St m a -> m (a, Ticks)
runStateT' m = do
  (a, St c) <- runStateT m $ St 0
  pure (a, c)

runCounterT :: Monad m => (forall s. CounterT s m a) -> m (Either String (a, Ticks))
runCounterT m = runSTT $ runExceptT $ runStateT' $ runT m

runCounterM :: (forall s. CounterM s a) -> Either String (a, Ticks)
runCounterM m = runIdentity $ runSTT $ runExceptT $ runStateT' $ runT m