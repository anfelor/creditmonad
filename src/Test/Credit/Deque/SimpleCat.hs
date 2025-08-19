module Test.Credit.Deque.SimpleCat where

import Prelude hiding (head, tail, concat)
import Prettyprinter (Pretty)
import Control.Monad
import Control.Monad.Credit
import Test.Credit (log2)
import Test.Credit.Deque.Base
import qualified Test.Credit.Deque.Base as D
import qualified Test.Credit.Deque.Bankers as D

-- | "simple"
data SimpleCat a m
  = Shallow (D.BDeque a m)
  | Deep (D.BDeque a m) -- ^ (>= 2 elements)
         (Thunk m (Lazy m) (SimpleCat (D.BDeque a m) m))
         (D.BDeque a m) -- ^ (>= 2 elements)

dangerous :: D.BDeque a m -> Bool
dangerous d = D.size d == 2

cost :: Credit
cost = qcost @(D.BDeque) undefined (Cons undefined) + 3 * qcost @(D.BDeque) undefined Uncons

danger :: D.BDeque a m -> Credit
danger d = if D.size d == 2 then cost else 0

deep :: MonadInherit m => D.BDeque a m -> Thunk m (Lazy m) (SimpleCat (D.BDeque a m) m) -> D.BDeque a m -> m (SimpleCat a m)
deep f m r = do
  m `hasAtLeast` (danger f + danger r)
  pure $ Deep f m r

isEmpty :: SimpleCat a m -> Bool
isEmpty (Shallow d) = D.isEmpty d
isEmpty (Deep _ _ _) = False

data DequeIs a m
  = Small (Maybe a)
  | Big (D.BDeque a m)

tooSmall :: MonadInherit m => D.BDeque a m -> m (DequeIs a m)
tooSmall d = do
  m1 <- D.uncons d
  case m1 of
    Nothing -> pure $ Small Nothing
    Just (x, d') -> do
      m2 <- D.uncons d'
      case m2 of
        Nothing -> pure $ Small (Just x)
        Just _ -> pure $ Big d

dappendL :: MonadInherit m => Maybe a -> D.BDeque a m -> m (D.BDeque a m)
dappendL Nothing d2 = pure d2
dappendL (Just x) d2 = D.cons x d2

dappendR :: MonadInherit m => D.BDeque a m -> Maybe a -> m (D.BDeque a m)
dappendR d1 Nothing = pure d1
dappendR d1 (Just x) = D.snoc d1 x

uncons' :: MonadInherit m => SimpleCat a m -> m (Maybe (a, Thunk m (Lazy m) (SimpleCat a m)))
uncons' (Shallow d) = tick >> do
  m <- D.uncons d
  case m of
    Nothing -> pure Nothing
    Just (x, d') -> fmap (Just . (x,)) $ delay $ Lazy $ do
      pure $ Shallow d'
uncons' (Deep f m r) = tick >> do
  f' <- D.uncons f
  case f' of
    Nothing -> pure Nothing
    Just (x, f') -> fmap (Just . (x,)) $ delay $ Lazy $ do
      dis <- tooSmall f'
      case dis of
        Big f' -> do
          when (dangerous f') $ m `creditWith` cost
          deep f' m r
        Small y -> do
          unless (dangerous r) $ m `creditWith` cost
          m' <- uncons' =<< force m
          case m' of
            Nothing -> Shallow <$> dappendL y r
            Just (h, t) -> do
              when (dangerous r) $ t `creditWith` cost
              dappendL y h >>= \h -> deep h t r

unsnoc' :: MonadInherit m => SimpleCat a m -> m (Maybe (Thunk m (Lazy m) (SimpleCat a m), a))
unsnoc' (Shallow d) = tick >> do
  m <- D.unsnoc d
  case m of
    Nothing -> pure Nothing
    Just (d', x) -> fmap (Just . (,x)) $ delay $ Lazy $ do
      pure $ Shallow d'
unsnoc' (Deep f m r) = tick >> do
  r' <- D.unsnoc r
  case r' of
    Nothing -> pure Nothing
    Just (r', x) -> fmap (Just . (,x)) $ delay $ Lazy $ do
      dis <- tooSmall r'
      case dis of
        Big r' -> do
          when (dangerous r') $ m `creditWith` cost
          deep f m r'
        Small y -> do
          unless (dangerous f) $ m `creditWith` cost
          m' <- unsnoc' =<< force m
          case m' of
            Nothing -> Shallow <$> dappendR f y
            Just (t, h) -> do
              when (dangerous f) $ t `creditWith` cost
              deep f t =<< dappendR h y

concat' :: MonadInherit m => SimpleCat a m -> SimpleCat a m -> m (SimpleCat a m)
concat' (Shallow d1) (Shallow d2) = tick >> do
  dis1 <- tooSmall d1
  case dis1 of
    Small y -> Shallow <$> dappendL y d2
    Big d1 -> do
      dis2 <- tooSmall d2
      case dis2 of
        Small y -> Shallow <$> dappendR d1 y
        Big d2 -> do
          m <- delay $ Lazy empty
          when (dangerous d1) $ m `creditWith` cost
          when (dangerous d2) $ m `creditWith` cost
          deep d1 m d2
concat' (Shallow d1) (Deep f m r) = tick >> do
  dis1 <- tooSmall d1
  case dis1 of
    Small y -> dappendL y f >>= \f -> deep f m r
    Big d -> do
      m `creditWith` cost
      unless (dangerous r) $ m `creditWith` cost
      m' <- delay $ Lazy $ cons f =<< force m
      when (dangerous d) $ m' `creditWith` cost
      when (dangerous r) $ m' `creditWith` cost
      deep d m' r
concat' (Deep f m r) (Shallow d2) = tick >> do
  dis2 <- tooSmall d2
  case dis2 of
    Small y -> deep f m =<< dappendR r y
    Big d -> do
      m `creditWith` cost
      unless (dangerous f) $ m `creditWith` cost
      m' <- delay $ Lazy $ flip snoc r =<< force m
      when (dangerous d) $ m' `creditWith` cost
      when (dangerous f) $ m' `creditWith` cost
      deep f m' d
concat' (Deep f1 m1 r1) (Deep f2 m2 r2) = tick >> do
  m <- delay $ Lazy $ do
    m1 `creditWith` (2 * cost)
    m1' <- flip snoc r1 =<< force m1
    m2 `creditWith` (2 * cost)
    m2' <- cons f2 =<< force m2
    concat' m1' m2'
  creditAllTo m
  deep f1 m r2

instance Deque SimpleCat where
  empty = Shallow <$> D.empty
  cons x (Shallow d) = Shallow <$> D.cons x d
  cons x (Deep f m r) = do
    f' <- D.cons x f
    deep f' m r
  snoc (Shallow d) x = Shallow <$> D.snoc d x
  snoc (Deep f m r) x = deep f m =<< D.snoc r x
  uncons d = do
    m <- uncons' d
    case m of
      Nothing -> pure Nothing
      Just (x, t) -> do
        t `creditWith` (2 * cost)
        Just . (x,) <$> force t
  unsnoc d = do
    m <- unsnoc' d
    case m of
      Nothing -> pure Nothing
      Just (t, x) -> do
        t `creditWith` (2 * cost)
        Just . (,x) <$> force t
  concat = concat'

instance BoundedDeque SimpleCat where
  qcost n (Cons x) = qcost @(D.BDeque) n (Cons x)
  qcost n (Snoc x) = qcost @(D.BDeque) n (Snoc x)
  qcost n Uncons = 1 + qcost @(D.BDeque) n Uncons + 2 * cost
  qcost n Unsnoc = 1 + qcost @(D.BDeque) n Unsnoc + 2 * cost
  qcost n Concat = cost + (1 + 6 * cost) * log2 n

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SimpleCat a m) where
  prettyCell (Shallow d) = do
    d' <- prettyCell d
    pure $ mkMCell "Shallow" [d']
  prettyCell (Deep f m r) = do
    f' <- prettyCell f
    m' <- prettyCell m
    r' <- prettyCell r
    pure $ mkMCell "Deep" [f', m', r']

instance Pretty a => MemoryStructure (SimpleCat (PrettyCell a)) where
  prettyStructure = prettyCell