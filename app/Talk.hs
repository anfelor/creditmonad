{-# LANGUAGE GADTs, LambdaCase #-}

-- Simplified version of Implicit Queue for the talk at the Haskell Symposium

module Talk where

import Prelude hiding (head, tail)
import Control.Monad (when, unless)
import Control.Monad.Credit
import Prettyprinter (Pretty, pretty)
import Control.Monad.Credit
import Test.Credit
import Test.QuickCheck

data QueueOp a = Push a | Pop
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (QueueOp a) where
  arbitrary = frequency
    [ (7, Push <$> arbitrary)
    , (3, pure Pop)
    ]

-- Main idea:
--  - snoc and tail both cost two credits
--  - the first credit is used to tick
--  - We maintain the invariant: In each queue Deep(f, m, r), m has 2 - (|f| - |r|) credits.
--  - The m thunk represents either a snoc or a tail, and thus requires two credits to force.
--  - snoc and tail spend their second credit on either the old m to be able to force it,
--    or on the new m to maintain the invariant.

data Digit a = Zero | One a | Two a a
  deriving (Eq, Ord)

data Talk a m
  = Empty | Deep (Digit a) (Thunk m (ILazyCon m) (Talk (a, a) m)) (Digit a)

data ILazyCon m a where
  IPush :: Pretty a => Talk a m -> a -> ILazyCon m (Talk a m)
  ITail :: Talk a m -> ILazyCon m (Talk a m)

instance MonadCredit m => HasStep (ILazyCon m) m where
  step (IPush q p) = push q p
  step (ITail q) = tail q

isEmpty :: Talk a m -> Bool
isEmpty Empty = True
isEmpty (Deep _ _ _) = False

head :: MonadCredit m => Talk a m -> m a
head q = case q of
  Deep (Two x _) _ _ -> pure x
  Deep (One x) _ _ -> pure x
  _ -> fail "head: empty queue"

size :: Digit a -> Credit
size = \case { Zero -> 0; One _ -> 1; Two _ _ -> 2 }

deep :: MonadCredit m => Digit a -> Thunk m (ILazyCon m) (Talk (a, a) m) -> Digit a -> m (Talk a m)
deep f m r = do
  m `hasAtLeast` (2 - size f + size r)
  pure $ Deep f m r

push :: (Pretty a, MonadCredit m) => Talk a m -> a -> m (Talk a m)
push q y = do
  tick
  case q of
    Empty -> do
      middle <- value $ Empty
      deep (One y) middle Zero
    Deep front middle Zero -> do
      middle `creditWith` 1
      deep front middle (One y)
    Deep front middle (One x) -> do
      when (size front == 2) $
        middle `creditWith` 1
      m <- force middle
      t <- delay $ IPush m (x, y)
      when (size front == 1) $
        t `creditWith` 1
      deep front t Zero
    _ -> fail "push: malformed queue"

fromDigit :: MonadCredit m => Digit a -> m (Talk a m)
fromDigit Zero = pure Empty
fromDigit (One x) = do
  m <- value Empty
  deep (One x) m Zero

tail :: MonadCredit m => Talk a m -> m (Talk a m)
tail q = tick >> case q of
  Deep (Two _ y) m rear -> do
    creditWith m 1
    deep (One y) m rear
  Deep (One _) m rear -> do
    unless (size rear == 1) $ creditWith m 1
    m' <- force m
    if isEmpty m'
      then fromDigit rear
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
          => Thunk m (ILazyCon m) (Talk a m) -> m String
showThunk t = lazymatch t showTalk $ \case
    IPush middle xy -> do
      m <- showTalk middle
      pure $ "(push " ++ m ++ " " ++ show xy ++ ")"
    ITail q -> do
      m <- showTalk q
      pure $ "(tail " ++ m ++ ")"

showTalk :: (MonadLazy m, Show a)
             => Talk a m -> m String
showTalk Empty = do
  pure $ "Empty"
showTalk (Deep f m r) = do
  m' <- showThunk m
  pure $ "(Deep " ++ show f ++ " " ++ m' ++ " "
                  ++ show r ++ ")"

instance (Arbitrary a, Show a, Pretty a) => DataStructure (Talk a) (QueueOp a) where
  cost _ (Push _) = 2
  cost _ Pop = 2
  create = pure $ Empty
  perform sz q (Push x) = (sz + 1,) <$> push q x
  perform sz q Pop =
    if isEmpty q
      then pure (0, Empty)
      else (sz - 1,) <$> tail q

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
  prettyCell (IPush t xy) = do
    t' <- prettyCell t
    let xy' = mkMCell (show $ pretty xy) []
    pure $ mkMCell "Push" [t', xy']
  prettyCell (ITail q) = do
    q' <- prettyCell q
    pure $ mkMCell "Tail" [q']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Talk a m) where
  prettyCell Empty = do
    pure $ mkMCell "Empty" []
  prettyCell (Deep f m r) = do
    f' <- prettyCell f
    m' <- prettyCell m
    r' <- prettyCell r
    pure $ mkMCell "Deep" [f', m', r']

instance Pretty a => MemoryStructure (Talk (PrettyCell a)) where
  prettyStructure = prettyCell