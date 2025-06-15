{-# LANGUAGE GADTs, LambdaCase #-}

module Test.Credit.Queue.Implicit where

import Prelude hiding (head, tail)
import Control.Monad (when, unless)
import Control.Monad.Credit
import Prettyprinter (Pretty)
import Test.Credit.Queue.Base

-- Main idea:
--  - snoc and tail both cost two credits
--  - the first credit is used to tick
--  - We maintain the invariant: In each queue Deep(f, m, r), m has 2 - (|f| - |r|) credits.
--  - The m thunk represents either a snoc or a tail, and thus requires two credits to force.
--  - snoc and tail spend their second credit on either the old m to be able to force it,
--    or on the new m to maintain the invariant.

data Digit a = Zero | One a | Two a a
  deriving (Eq, Ord)

data Implicit a m
  = Shallow (Digit a)
  | Deep (Digit a) (Thunk m (ILazyCon m) (Implicit (a, a) m)) (Digit a)

data ILazyCon m a where
  IPure :: a -> ILazyCon m a
  ISnoc :: Thunk m (ILazyCon m) (Implicit a m) -> a -> ILazyCon m (Implicit a m)
  ITail :: Implicit a m -> ILazyCon m (Implicit a m)

instance MonadCredit m => HasStep (ILazyCon m) m where
  step (IPure x) = pure x
  step (ISnoc t p) = do
    q <- force t
    snoc' q p
  step (ITail q) = tail q

isEmpty :: Implicit a m -> Bool
isEmpty (Shallow Zero) = True
isEmpty _ = False

head :: MonadCredit m => Implicit a m -> m a
head q = case q of
  Shallow (One x) -> pure x
  Deep (Two x _) _ _ -> pure x
  Deep (One x) _ _ -> pure x
  _ -> fail "head: empty queue"

size :: Digit a -> Credit
size = \case { Zero -> 0; One _ -> 1; Two _ _ -> 2 }

deep :: MonadCredit m => Digit a -> Thunk m (ILazyCon m) (Implicit (a, a) m) -> Digit a -> m (Implicit a m)
deep f m r = do
  m `hasAtLeast` (2 - size f + size r)
  pure $ Deep f m r

snoc' :: MonadCredit m => Implicit a m -> a -> m (Implicit a m)
snoc' q y = do
  tick
  case q of
    Shallow Zero -> pure $ Shallow (One y)
    Shallow (One x) -> do
      middle <- delay $ IPure $ Shallow Zero
      deep (Two x y) middle Zero
    Deep front middle Zero -> do
      middle `creditWith` 1
      deep front middle (One y)
    Deep front middle (One x) -> do
      middle `hasAtLeast` (2 - size front + 1)
      t <- delay $ ISnoc middle (x, y)
      if size front == 1
        then t      `creditWith` 1
        else middle `creditWith` 1
      deep front t Zero
    _ -> fail "snoc: malformed queue"

tail :: MonadCredit m => Implicit a m -> m (Implicit a m)
tail q = tick >> case q of
  Shallow (One _) -> pure $ Shallow Zero
  Deep (Two _ y) m rear -> do
    creditWith m 1
    deep (One y) m rear
  Deep (One _) m rear -> do
    unless (size rear == 1) $ creditWith m 1
    m' <- force m
    if isEmpty m'
      then pure $ Shallow rear
      else do
        (y, z) <- head m'
        t <- delay $ ITail m'
        when (size rear == 1) $ creditWith t 1
        deep (Two y z) t rear
  _ -> fail "tail: empty queue"

instance Show a => Show (Digit a) where
  show Zero = "Zero"
  show (One a) = "(One " ++ show a ++ ")"
  show (Two a b) = "(Two " ++ show a ++ " " ++ show b ++ ")"

showThunk :: (MonadLazy m, Show a)
          => Thunk m (ILazyCon m) (Implicit a m) -> m String
showThunk t = lazymatch t showImplicit $ \case
    IPure a -> showImplicit a
    ISnoc middle xy -> do
      m <- showThunk middle
      pure $ "(snoc " ++ m ++ " " ++ show xy ++ ")"
    ITail q -> do
      m <- showImplicit q
      pure $ "(tail " ++ m ++ ")"

showImplicit :: (MonadLazy m, Show a)
             => Implicit a m -> m String
showImplicit (Shallow d) = do
  pure $ "(Shallow " ++ show d ++ ")"
showImplicit (Deep f m r) = do
  m' <- showThunk m
  pure $ "(Deep " ++ show f ++ " " ++ m' ++ " "
                  ++ show r ++ ")"

instance Queue Implicit where
  empty = pure $ Shallow Zero
  snoc q y = snoc' q y
  uncons q =
    if isEmpty q
      then pure Nothing
      else do
        h <- head q
        t <- tail q
        pure $ Just (h, t)

instance BoundedQueue Implicit where
  qcost _ (Snoc _) = 2
  qcost _ Uncons = 2

instance MemoryCell m a => MemoryCell m (Digit a) where
  prettyCell Zero = pure $ mkMCell "Zero" []
  prettyCell (One a) = do
    a' <- prettyCell a
    pure $ mkMCell "One" [a']
  prettyCell (Two a b) = do
    a' <- prettyCell a
    b' <- prettyCell b
    pure $ mkMCell "Two" [a', b']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (ILazyCon m a) where
  prettyCell (IPure x) = do
    x' <- prettyCell x
    pure $ mkMCell "IPure" [x']
  prettyCell (ISnoc t _) = do
    t' <- prettyCell t
    pure $ mkMCell "ISnoc" [t']
  prettyCell (ITail q) = do
    q' <- prettyCell q
    pure $ mkMCell "ITail" [q']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Implicit a m) where
  prettyCell (Shallow d) = do
    d' <- prettyCell d
    pure $ mkMCell "Shallow" [d']
  prettyCell (Deep f m r) = do
    f' <- prettyCell f
    m' <- prettyCell m
    r' <- prettyCell r
    pure $ mkMCell "Deep" [f', m', r']

instance Pretty a => MemoryStructure (Implicit (PrettyCell a)) where
  prettyStructure = prettyCell