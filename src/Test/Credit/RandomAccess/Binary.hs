{-# LANGUAGE TypeFamilies #-}

module Test.Credit.RandomAccess.Binary where

import Prelude hiding (lookup)
import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.RandomAccess.Base

data Stream m a
  = SCons a (Stream m a)
  | SNil
  | SIndirect (Thunk m (Lazy m) (Stream m a))

indirect :: MonadCredit m => m (Stream m a) -> m (Stream m a)
indirect = fmap SIndirect . delay . Lazy

credit :: MonadCredit m => Credit -> Stream m a -> m ()
credit cr (SIndirect i) = creditWith i cr
credit _ _ = pure ()

-- | Smart destructor for streams, consuming one credit
smatch :: MonadCredit m => Stream m a -- ^ Scrutinee
       -> m b -- ^ Nil case
       -> (a -> Stream m a -> m b) -- ^ Cons case
       -> m b
smatch x nil cons = tick >> eval x
  where
    eval x = case x of
      SCons a as -> cons a as
      SNil -> nil
      SIndirect i -> force i >>= eval

data Tree a = Leaf a | Node Int (Tree a) (Tree a)
  deriving (Eq, Ord, Show)

data Digit a = Zero | One (Tree a) | Two (Tree a) (Tree a)
  deriving (Eq, Ord, Show)

size :: Tree a -> Int
size (Leaf _) = 1
size (Node w _ _) = w

link :: Tree a -> Tree a -> Tree a
link t1 t2 = Node (size t1 + size t2) t1 t2

consTree :: MonadCredit m => Tree a -> Stream m (Digit a) -> m (Stream m (Digit a))
consTree t ts = smatch ts
  (pure $ SCons (One t) SNil)
  (\d ds -> case d of
    Zero -> pure $ SCons (One t) ds
    One t' -> credit 1 ds >> pure (SCons (Two t t') ds)
    Two t2 t3 -> do
      ds' <- indirect $ consTree (link t2 t3) ds
      credit 1 ds'
      pure $ SCons (One t) ds')

unconsTree :: MonadCredit m => Stream m (Digit a) -> m (Maybe (Tree a, Stream m (Digit a)))
unconsTree ts = smatch ts
  (pure Nothing)
  (\d ds -> case d of
    One t -> credit 1 ds >> smatch ds
      (pure $ Just (t, SNil))
      (\_ _ -> pure $ Just (t, SCons Zero ds))
    Two t t' -> pure $ Just (t, SCons (One t') ds)
    Zero -> do
      ds' <- unconsTree ds
      case ds' of
        Just (Node _ t1 t2, ds'') -> pure $ Just (t1, SCons (One t2) ds'')
        _ -> pure Nothing)

lookupTree :: MonadCredit m => Int -> Tree a -> m (Maybe a)
lookupTree 0 (Leaf x) = pure $ Just x
lookupTree i (Leaf _) = pure Nothing
lookupTree i (Node w t1 t2)
  | i < w `div` 2 = tick >> lookupTree i t1
  | otherwise = tick >> lookupTree (i - w `div` 2) t2

updateTree :: MonadCredit m => Int -> a -> Tree a -> m (Tree a)
updateTree 0 y (Leaf _) = pure $ Leaf y
updateTree i _ (Leaf x) = pure $ Leaf x
updateTree i y (Node w t1 t2)
  | i < w `div` 2 = tick >> do
      t1' <- updateTree i y t1
      pure $ Node w t1' t2
  | otherwise = tick >> do
      t2' <- updateTree (i - w `div` 2) y t2
      pure $ Node w t1 t2'

newtype BinaryRA a m = BinaryRA { unBinaryRA :: Stream m (Digit a) }

instance RandomAccess BinaryRA where
  empty = pure $ BinaryRA SNil
  cons x (BinaryRA ts) = BinaryRA <$> consTree (Leaf x) ts
  uncons (BinaryRA ts) = do
    m <- unconsTree ts
    case m of
      Just (Leaf x, ts') -> pure $ Just (x, BinaryRA ts')
      _ -> pure Nothing
  lookup i (BinaryRA ts) = smatch ts
    (pure Nothing)
    (\d ds -> case d of
      Zero -> lookup i (BinaryRA ds)
      One t ->
        if i < size t
          then lookupTree i t
          else credit 1 ds >> lookup (i - size t) (BinaryRA ds)
      Two t1 t2 ->
        if i < size t1
          then lookupTree i t1
          else let j = i - size t1 in
            if j < size t2
              then lookupTree j t2
              else lookup (j - size t2) (BinaryRA ds))
  update i y (BinaryRA ts) = smatch ts
    (pure $ BinaryRA SNil)
    (\d ds -> case d of
      Zero -> BinaryRA . (SCons Zero) . unBinaryRA <$> update i y (BinaryRA ds)
      One t ->
        if i < size t
          then BinaryRA . (flip SCons ds) . One <$> updateTree i y t
          else credit 1 ds >> BinaryRA . (SCons (One t)) . unBinaryRA <$> update (i - size t) y (BinaryRA ds)
      Two t1 t2 ->
        if i < size t1
          then BinaryRA . (flip SCons ds) . flip Two t2 <$> updateTree i y t1
          else let j = i - size t1 in
            if j < size t2
              then BinaryRA . (flip SCons ds) . Two t1 <$> updateTree j y t2
              else BinaryRA . (SCons (Two t1 t2)) . unBinaryRA <$> update (j - size t2) y (BinaryRA ds))

instance BoundedRandomAccess BinaryRA where
  qcost n (Cons _) = 2
  qcost n Uncons = 3 + log2 n
  qcost n (Lookup _) = 1 + 3 * log2 n
  qcost n (Update _ _) = 1 + 3 * log2 n

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Stream m a) where
  prettyCell xs = mkMList <$> toList xs <*> toHole xs
    where
      toList SNil = pure $ []
      toList (SCons x xs) = (:) <$> prettyCell x <*> toList xs
      toList (SIndirect t) = pure $ []

      toHole SNil = pure $ Nothing
      toHole (SCons x xs) = toHole xs
      toHole (SIndirect t) = Just <$> prettyCell t

instance MemoryCell m a => MemoryCell m (Tree a) where
  prettyCell (Leaf x) = do
    x' <- prettyCell x
    pure $ mkMCell "Leaf" [x']
  prettyCell (Node w t1 t2) = do
    t1' <- prettyCell t1
    t2' <- prettyCell t2
    pure $ mkMCell "Node" [t1', t2']

instance MemoryCell m a => MemoryCell m (Digit a) where
  prettyCell Zero = pure $ mkMCell "Zero" []
  prettyCell (One t) = do
    t' <- prettyCell t
    pure $ mkMCell "One" [t']
  prettyCell (Two t1 t2) = do
    t1' <- prettyCell t1
    t2' <- prettyCell t2
    pure $ mkMCell "Two" [t1', t2']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (BinaryRA a m) where
  prettyCell (BinaryRA ts) = do
    ts' <- prettyCell ts
    pure $ mkMCell "BinaryRA" [ts']

instance Pretty a => MemoryStructure (BinaryRA (PrettyCell a)) where
  prettyStructure = prettyCell