{-# LANGUAGE TypeFamilies, StandaloneDeriving, UndecidableInstances, OverloadedStrings, DerivingStrategies, MagicHash #-}

module Control.Monad.Credit.CreditM (CreditM, Error(..), runCreditM, CreditT, runCreditT, resetCurrentThunk) where

import Prelude hiding (lookup)
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State.Lazy
import Control.Monad.ST.Trans
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import GHC.Exts
import Prettyprinter

import Control.Monad.Credit.Base

-- Errors

data Error
  = OutOfCredits Cell
  | InvalidAccount Cell
  | InvalidTick Cell
  | ClosedCurrent Cell
  | UserError String
  | AssertionFailed Cell Credit Credit
  deriving (Eq, Ord, Show)

-- Each memory cell has an associated amount of credits
-- Once it is evaluated, it chooses an heir to pass its credits on to

data Account = Balance
                 Int# -- ^ The amount of credits in the account
                 Int# -- ^ The number of credits consumed so far
             | Closed
             | ClosedWithHeir {-# UNPACK #-} !Cell Int#
  deriving (Eq, Ord, Show)

newtype Credits = Credits (IntMap Account)
  deriving (Eq, Ord, Show)

open :: Cell -> Credits -> Credits
open (Cell i) (Credits cm) = Credits (IntMap.insert i (Balance 0# 0#) cm)

addCredit :: Cell -> Credit -> Credits -> Credits
addCredit (Cell i) (Credit (I# n)) (Credits cm) = go i cm
  where
    go i cm =
      case IntMap.lookup i cm of
        Just (Balance avail burnt) -> Credits (IntMap.insert i (Balance (n +# avail) burnt) cm)
        Just (ClosedWithHeir (Cell h) burnt) ->
          case IntMap.lookup h cm of
            Just (ClosedWithHeir (Cell h') burnt') -> -- path halving
              go h' (IntMap.insert i (ClosedWithHeir (Cell h') (burnt +# burnt')) cm)
            _ -> go h cm
        Just Closed -> Credits cm
        Nothing -> Credits cm

subCredit :: MonadError Error m => Cell -> Credit -> Credits -> m Credits
subCredit (Cell i) (Credit (I# n)) (Credits cm) = go i cm
  where
    go i cm = case IntMap.lookup i cm of
      Just (Balance avail burnt) ->
        if isTrue# $ avail -# n <# 0#
          then throwError (OutOfCredits (Cell i))
          else pure (Credits (IntMap.insert i (Balance (avail -# n) (burnt +# n)) cm))
      Just (ClosedWithHeir (Cell h) _) -> go h cm
      Just Closed -> throwError (InvalidTick (Cell i))
      Nothing -> throwError (InvalidTick (Cell i))

-- | Close an account
close :: MonadError Error m => Cell -> Credits -> m Credits
close (Cell i) (Credits cm) = do
  case IntMap.lookup i cm of
    Just (Balance _ _) -> pure $ Credits $ IntMap.insert i Closed cm
    Just Closed -> pure $ Credits cm
    Just (ClosedWithHeir _ _) -> pure $ Credits cm
    Nothing -> throwError (InvalidAccount (Cell i))

-- | Close an account and transfer its credits to the heir.
closeWithHeir :: MonadError Error m => Cell -> Cell -> Credits -> m Credits
closeWithHeir (Cell i) h c = do
  (n, burnt) <- extractValue c
  pure $ closeAccount burnt $ addCredit h n c
  where
    closeAccount (I# burnt) (Credits cm) = Credits $ IntMap.insert i (ClosedWithHeir h burnt) cm

    extractValue (Credits cm) =
      case IntMap.findWithDefault (Balance 0# 0#) i cm of
        Balance a b -> pure (Credit (I# a), I# b)
        ClosedWithHeir _ _ -> throwError (InvalidAccount (Cell i))
        Closed -> throwError (InvalidAccount (Cell i))

singleton :: Cell -> Credit -> Credits
singleton (Cell i) (Credit (I# n)) = Credits (IntMap.singleton i (Balance n 0#))

-- Run computation in a state monad

-- State of the computation
-- me: The currently evaluated cell
-- credits: The credits of each cell
-- next: The next free cell to be allocated
data St = St {-# UNPACK #-} !Cell !Credits {-# UNPACK #-} !Int 
  deriving (Eq, Ord, Show)

-- | An instance of the credit monad using ST to memoize thunks.
type CreditM s = CreditT s Identity

-- | A monad transformer on the credit monad.
-- Warning! This monad transformer includes the ST monad transformer and
-- should not be used with monads that can contain multiple answers,
-- like the list monad. Safe monads include the monads State, Reader, Writer,
-- Maybe and combinations of their corresponding monad transformers.
newtype CreditT s m a = CreditT { runT :: ExceptT Error (StateT St (STT s m)) a }

instance Functor m => Functor (CreditT s m) where
  fmap f (CreditT m) = CreditT (fmap f m)

instance Monad m => Applicative (CreditT s m) where
  pure = CreditT . pure
  CreditT f <*> CreditT x = CreditT (f <*> x)

instance Monad m => Monad (CreditT s m) where
  CreditT m >>= f = CreditT (m >>= runT . f)

instance Monad m => MonadError Error (CreditT s m) where
  throwError e = CreditT (throwError e)
  catchError (CreditT m) h = CreditT (catchError m (runT . h))

instance Monad m => MonadState St (CreditT s m) where
  get = CreditT get
  put s = CreditT (put s)

instance MonadTrans (CreditT s) where
  lift = CreditT . lift . lift . lift

liftST :: Monad m => STT s m a -> CreditT s m a
liftST = CreditT . lift . lift

getMe :: Monad m => CreditT s m Cell
getMe = do
  St me _ _ <- get
  pure me

getNext :: Monad m => CreditT s m Cell
getNext = do
  St _ _ nxt <- get
  modify' $ \(St me c _) -> St me c (nxt + 1)
  pure $ Cell nxt

withCredits :: Monad m => (Credits -> CreditT s m Credits) -> CreditT s m ()
withCredits f = do
  St _ c _ <- get
  c' <- f c
  modify' $ \(St me _ nxt) -> St me c' nxt

instance Monad m => MonadFail (CreditT s m) where
  fail e = throwError (UserError e)

instance Monad m => MonadCount (CreditT s m) where
  tick = do
    me <- getMe
    withCredits $ subCredit me 1

instance Monad m => MonadLazy (CreditT s m) where
  {-# SPECIALIZE instance MonadLazy (CreditT s Identity) #-}
  {-# SPECIALIZE instance MonadLazy (CreditT s (State st)) #-}
  data Thunk (CreditT s m) t b = Thunk !Cell !(STRef s (Either (t b) b))
  delay a = do
    i <- getNext
    withCredits $ pure . open i
    s <- liftST $ newSTRef (Left a)
    pure (Thunk i s)
  value b = do
    i <- getNext
    withCredits $ pure . open i
    s <- liftST $ newSTRef (Right b)
    pure (Thunk i s)
  force (Thunk i t) = do
    t' <- liftST $ readSTRef t
    case t' of
      Left a -> do  -- [step] rule in the big-step semantics of the paper
        St me _ _ <- get
        modify' $ \(St _ c nxt) -> St i c nxt
        b <- step a
        modify' $ \(St _ c nxt) -> St me c nxt
        liftST $ writeSTRef t (Right b)
        withCredits $ close i
        pure b
      Right b -> pure b
  lazymatch (Thunk _ t) f g = do
    t' <- liftST $ readSTRef t
    case t' of
      Right b -> f b
      Left a -> g a

assertAtLeast :: Monad m => Cell -> Credit -> CreditT s m ()
assertAtLeast (Cell i) n = do
  St _ (Credits cm) _ <- get
  case IntMap.lookup i cm of
    Just (Balance m' _) -> do
      let m = Credit (I# m')
      if m >= n
        then pure ()
        else throwError (AssertionFailed (Cell i) n m)
    Just Closed -> pure ()
    Just (ClosedWithHeir i burnt) ->
      assertAtLeast i (n - Credit (I# burnt))
    Nothing -> throwError (InvalidAccount (Cell i))

instance Monad m => MonadCredit (CreditT s m) where
  {-# SPECIALIZE instance MonadCredit (CreditT s Identity) #-}
  {-# SPECIALIZE instance MonadCredit (CreditT s (State st)) #-}
  creditWith (Thunk i _) n =
    if n > 0 then do
      me <- getMe
      withCredits $ subCredit me n . addCredit i n
    else pure ()
  hasAtLeast (Thunk i _) n =
    assertAtLeast i n

instance Monad m => MonadInherit (CreditT s m) where
  {-# SPECIALIZE instance MonadInherit (CreditT s Identity) #-}
  {-# SPECIALIZE instance MonadInherit (CreditT s (State st)) #-}
  creditAllTo (Thunk i _) = do
    me <- getMe
    withCredits $ me `closeWithHeir` i

emptyState :: Credit -> St
emptyState n = St (Cell 0) (singleton (Cell 0) n) 1

runCreditT :: Monad m => Credit -> (forall s. CreditT s m a) -> m (Either Error a)
runCreditT n m = runSTT $ evalStateT (runExceptT (runT m)) (emptyState n)

runCreditM :: Credit -> (forall s. CreditM s a) -> Either Error a
runCreditM n m = runIdentity $ runSTT $ evalStateT (runExceptT (runT m)) (emptyState n)

{-# SPECIALIZE resetCurrentThunk :: Credit -> CreditT s Identity () #-}
{-# SPECIALIZE resetCurrentThunk :: Credit -> CreditT s (State st) () #-}
resetCurrentThunk :: Monad m => Credit -> CreditT s m ()
resetCurrentThunk (Credit (I# n)) = do
  (Cell me) <- getMe
  withCredits $ \(Credits c) -> do
    case IntMap.lookup me c of
      Just (Balance m b) -> pure $ Credits $ IntMap.insert me (Balance (n +# m) b) c
      _ -> throwError $ ClosedCurrent (Cell me)

-- Pretty Printing

getCredit :: Monad m => Cell -> CreditT s m Credit
getCredit (Cell i) = do
  St _ (Credits cm) _ <- get
  case IntMap.lookup i cm of
    Just (Balance n _) -> pure $ Credit (I# n)
    _ -> pure 0

instance (Monad m) => MonadMemory (CreditT s m) where
  {-# SPECIALIZE instance MonadMemory (CreditT s Identity) #-}
  {-# SPECIALIZE instance MonadMemory (CreditT s (State st)) #-}
  prettyThunk (Thunk c s) = do
    e <- liftST $ readSTRef s
    (Memory mtree mstore) <- case e of
      Left a -> prettyCell a
      Right b -> prettyCell b
    cr <- getCredit c
    pure $ Memory (Indirection c) (Map.insert c (mtree, cr) mstore)

instance Pretty Error where
  pretty (OutOfCredits i) = "Out of credits for" <+> pretty i
  pretty (InvalidAccount i) = "Invalid account for" <+> pretty i
  pretty (InvalidTick i) = "Invalid tick for" <+> pretty i
  pretty (ClosedCurrent (Cell 0)) = "Closed main thread account. Never invoke creditAllTo on main thread."
  pretty (ClosedCurrent i) = "Closed current account" <+> pretty i
  pretty (UserError e) = "User error:" <+> pretty e
  pretty (AssertionFailed i n m) = pretty i <+> "should have" <+> pretty n <+> "credits but only has" <+> pretty m

instance Pretty a => Pretty (Either Error a) where
  pretty (Left e) = pretty e
  pretty (Right a) = pretty a

instance Pretty Account where
  pretty (Balance n _) = pretty (I# n)
  pretty Closed = "closed"
  pretty (ClosedWithHeir h _) = "closed with heir" <+> pretty h

instance Pretty Credits where
  pretty (Credits cm) = vsep $ map prettyPair (IntMap.toList cm)
    where
      prettyPair (i, a) = pretty i <+> "->" <+> pretty a

instance Pretty St where
  pretty (St me c nxt) = vsep
    [ "me:" <+> pretty me
    , "credits:" <+> pretty c
    , "next:" <+> pretty nxt
    ]