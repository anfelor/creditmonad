{-# LANGUAGE TypeFamilies #-}

module Test.Credit.RandomAccess.Zeroless where

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

data Digit a = One (Tree a) | Two (Tree a) (Tree a) | Three (Tree a) (Tree a) (Tree a)
  deriving (Eq, Ord, Show)

size :: Tree a -> Int
size (Leaf _) = 1
size (Node w _ _) = w

link :: Tree a -> Tree a -> Tree a
link t1 t2 = Node (size t1 + size t2) t1 t2

consTree :: MonadCredit m => Tree a -> Stream m (Digit a) -> m (Stream m (Digit a))
consTree t1 ts = smatch ts
  (pure $ SCons (One t1) SNil)
  (\d ds -> case d of
    One t2 -> pure $ SCons (Two t1 t2) ds
    Two t2 t3 -> credit 2 ds >> pure (SCons (Three t1 t2 t3) ds)
    Three t2 t3 t4 -> do
      ds' <- indirect $ consTree (link t3 t4) ds
      credit 2 ds'
      pure $ SCons (Two t1 t2) ds')

unconsTree :: MonadCredit m => Stream m (Digit a) -> m (Maybe (Tree a, Stream m (Digit a)))
unconsTree ts = smatch ts
  (pure Nothing)
  (\d ds -> case d of
      One t -> smatch ds
        (pure $ Just (t, SNil))
        (\_ _ -> do
          ds' <- indirect $ do
            ds' <- unconsTree ds
            case ds' of
              Just (Node _ t1 t2, ds'') -> do
                pure $ SCons (Two t1 t2) ds''
              Nothing -> fail "unconsTree: malformed tree"
          credit 2 ds'
          pure $ Just (t, ds'))
      Two t1 t2 -> credit 2 ds >> pure (Just (t1, SCons (One t2) ds))
      Three t1 t2 t3 -> pure $ Just (t1, SCons (Two t2 t3) ds))

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

newtype ZerolessRA a m = ZerolessRA { unZerolessRA :: Stream m (Digit a) }

instance RandomAccess ZerolessRA where
  empty = pure $ ZerolessRA SNil
  cons x (ZerolessRA ts) = credit 2 ts >> ZerolessRA <$> consTree (Leaf x) ts
  uncons (ZerolessRA ts) = credit 2 ts >> do
    m <- unconsTree ts
    case m of
      Just (Leaf x, ts') -> pure $ Just (x, ZerolessRA ts')
      _ -> pure Nothing
  lookup i (ZerolessRA ts) = credit 2 ts >> smatch ts
    (pure Nothing)
    (\d ds -> case d of
      One t -> do
        if i < size t
          then lookupTree i t
          else lookup (i - size t) (ZerolessRA ds)
      Two t1 t2 -> do
        if i < size t1
          then lookupTree i t1
          else let j = i - size t1 in
            if j < size t2
              then lookupTree j t2
              else credit 2 ds >> lookup (j - size t2) (ZerolessRA ds)
      Three t1 t2 t3 -> do
        if i < size t1
          then lookupTree i t1
          else let j = i - size t1 in
            if j < size t2
              then lookupTree j t2
              else let k = j - size t2 in
                if k < size t3
                  then lookupTree k t3
                  else lookup (k - size t3) (ZerolessRA ds))
  update i y (ZerolessRA ts) = credit 2 ts >> smatch ts
    (pure $ ZerolessRA SNil)
    (\d ds -> case d of
        One t -> do
            if i < size t
              then ZerolessRA . (flip SCons ds) . One <$> updateTree i y t
              else ZerolessRA . (SCons (One t)) . unZerolessRA <$> update (i - size t) y (ZerolessRA ds)
        Two t1 t2 -> do
            if i < size t1
              then ZerolessRA . (flip SCons ds) . flip Two t2 <$> updateTree i y t1
              else let j = i - size t1 in
                if j < size t2
                  then ZerolessRA . (flip SCons ds) . Two t1 <$> updateTree j y t2
                  else credit 2 ds >> ZerolessRA . (SCons (Two t1 t2)) . unZerolessRA <$> update (j - size t2) y (ZerolessRA ds)
        Three t1 t2 t3 -> do
            if i < size t1
              then ZerolessRA . (flip SCons ds) . (\t1' -> Three t1' t2 t3) <$> updateTree i y t1
              else let j = i - size t1 in
                if j < size t2
                  then ZerolessRA . (flip SCons ds) . (\t2' -> Three t1 t2' t3) <$> updateTree j y t2
                  else let k = j - size t2 in
                    if k < size t3
                      then ZerolessRA . (flip SCons ds) . Three t1 t2 <$> updateTree k y t3
                      else ZerolessRA . (SCons (Three t1 t2 t3)) . unZerolessRA <$> update (k - size t3) y (ZerolessRA ds))

instance BoundedRandomAccess ZerolessRA where
  qcost n (Cons _) = 5
  qcost n Uncons = 6
  qcost _ (Lookup i) = 3 + 5 * log2 (fromIntegral i * 2)
  qcost _ (Update i _) = 3 + 5 * log2 (fromIntegral i * 2)

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
  prettyCell (One t) = do
    t' <- prettyCell t
    pure $ mkMCell "One" [t']
  prettyCell (Two t1 t2) = do
    t1' <- prettyCell t1
    t2' <- prettyCell t2
    pure $ mkMCell "Two" [t1', t2']
  prettyCell (Three t1 t2 t3) = do
    t1' <- prettyCell t1
    t2' <- prettyCell t2
    t3' <- prettyCell t3
    pure $ mkMCell "Three" [t1', t2', t3']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (ZerolessRA a m) where
  prettyCell (ZerolessRA ts) = do
    ts' <- prettyCell ts
    pure $ mkMCell "ZerolessRA" [ts']

instance Pretty a => MemoryStructure (ZerolessRA (PrettyCell a)) where
  prettyStructure = prettyCell