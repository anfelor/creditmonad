{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances, TypeApplications, QuantifiedConstraints #-}

module Test.Credit.Finger.Base where

import Prelude hiding (head, tail, last, init, concat)

import Control.Monad.Credit
import qualified Test.Credit as C
import qualified Test.Credit.Deque.Base as D
import qualified Test.Credit.Heap.Base as H
import qualified Test.Credit.RandomAccess.Base as RA
import qualified Test.Credit.Sortable.Base as S

class (Eq v, Monoid v) => Measured a v where
  measure :: a -> v

instance Measured a v => Measured [a] v where
  measure = mconcat . map measure

instance (Measured a v, Measured b v) => Measured (a, b) v where
  measure (x, y) = measure x <> measure y

instance (Measured a v, Measured b v, Measured c v) => Measured (a, b, c) v where
  measure (x, y, z) = measure x <> measure y <> measure z

instance (Measured a v, Measured b v) => Measured (Either a b) v where
  measure (Left x) = measure x
  measure (Right y) = measure y

instance Measured a v => Measured (Maybe a) v where
  measure Nothing = mempty
  measure (Just a) = measure a

data Split f v a m = Split
  { smaller :: f v a m
  , found   :: a
  , bigger  :: f v a m
  }

class (forall a v m. Measured a v => Measured (f v a m) v) => FingerTree f where
  empty :: f v a m
  isEmpty :: f v a m -> Bool

  cons :: (MonadCredit m, Measured a v)
       => a -> f v a m -> m (f v a m)
  head :: (MonadCredit m, Measured a v)
       => f v a m -> m a
  tail :: (MonadCredit m, Measured a v)
       => f v a m -> m (f v a m)

  snoc :: (MonadCredit m, Measured a v)
       => f v a m -> a -> m (f v a m)
  last :: (MonadCredit m, Measured a v)
       => f v a m -> m a
  init :: (MonadCredit m, Measured a v)
       => f v a m -> m (f v a m)

  concat :: (MonadCredit m, Measured a v)
         => f v a m -> f v a m -> m (f v a m)

  splitTree :: (MonadCredit m, Measured a v)
            => (v -> Bool) -> v -> f v a m -> m (Split f v a m)

  treeToList :: (MonadCredit m, Measured a v)
             => f v a m -> m [a]

data FingerOp = Cons | Head | Tail | Snoc | Last | Init | Concat | SplitTree | TreeToList
  deriving (Eq, Ord, Show)

class FingerTree f => BoundedFingerTree f where
  fcost :: C.Size -> FingerOp -> Credit

fcostUncons :: forall f. BoundedFingerTree f => C.Size -> Credit
fcostUncons n = fcost @f n Head + fcost @f n Tail

fcostUnsnoc :: forall f. BoundedFingerTree f => C.Size -> Credit
fcostUnsnoc n = fcost @f n Last + fcost @f n Init

uncons :: (MonadCredit m, Measured a v, FingerTree f) => f v a m -> m (Maybe (a, f v a m))
uncons q =
  if isEmpty q
    then pure Nothing
    else do
      h <- head q
      t <- tail q
      pure $ Just (h, t)

unsnoc :: (MonadCredit m, Measured a v, FingerTree f) => f v a m -> m (Maybe (f v a m, a))
unsnoc q =
  if isEmpty q
    then pure Nothing
    else do
      h <- last q
      t <- init q
      pure $ Just (t, h)

split :: (MonadCredit m, Measured a v, FingerTree f) => (v -> Bool) -> f v a m -> m (f v a m, f v a m)
split p xs =
  if isEmpty xs
    then pure (empty, empty)
    else do
      if p (measure xs)
        then do (Split l x r) <- splitTree p mempty xs
                (l,) <$> cons x r
        else pure (xs, empty)

takeUntil :: (MonadCredit m, Measured a v, FingerTree f) => (v -> Bool) -> f v a m -> m (f v a m)
takeUntil p m = fst <$> split p m

dropUntil :: (MonadCredit m, Measured a v, FingerTree f) => (v -> Bool) -> f v a m -> m (f v a m)
dropUntil p m = snd <$> split p m

lookupTree :: (MonadCredit m, Measured a v, FingerTree f) => (v -> Bool) -> v -> f v a m -> m (Maybe (v, a))
lookupTree p i xs =
  if isEmpty xs
    then pure Nothing
    else do
      (Split l x _) <- splitTree p i xs
      let ml = measure l
      pure $ Just (i <> ml, x)

newtype Elem a = Elem a
  deriving (Eq, Ord, Show)

instance (MemoryCell m a) => MemoryCell m (Elem a) where
  prettyCell (Elem x) = prettyCell x

-- Deque

instance Measured (Elem a) () where
  measure (Elem x) = ()

newtype FingerDeque f a m = FingerDeque (f () (Elem a) m)

instance FingerTree f => D.Deque (FingerDeque f) where
  empty = pure $ FingerDeque empty
  cons x (FingerDeque q) = FingerDeque <$> cons (Elem x) q
  snoc (FingerDeque q) x = FingerDeque <$> snoc q (Elem x)
  uncons (FingerDeque q) = do
    m <- uncons q
    case m of
      Nothing -> pure Nothing
      Just (Elem x, q') -> pure $ Just (x, FingerDeque q')
  unsnoc (FingerDeque q) = do
    m <- unsnoc q
    case m of
      Nothing -> pure Nothing
      Just (q', Elem x) -> pure $ Just (FingerDeque q', x)
  concat (FingerDeque q1) (FingerDeque q2) = FingerDeque <$> concat q1 q2

instance BoundedFingerTree f => D.BoundedDeque (FingerDeque f) where
  qcost n (D.Cons _) = fcost @f n Cons
  qcost n (D.Snoc _) = fcost @f n Snoc
  qcost n D.Uncons = fcostUncons @f n
  qcost n D.Unsnoc = fcostUnsnoc @f n
  qcost n D.Concat = fcost @f n Concat

instance (MonadMemory m, MemoryCell m (f () (Elem a) m)) => MemoryCell m (FingerDeque f a m) where
  prettyCell (FingerDeque q) = prettyCell q

instance (MemoryStructure (f () (Elem a))) => MemoryStructure (FingerDeque f a) where
  prettyStructure = prettyStructure

-- Random Access

newtype Size = Size Int
  deriving (Eq, Ord, Show, Num)

instance Semigroup Size where
  x <> y = x + y

instance Monoid Size where
  mempty = 0

instance Measured (Elem a) Size where
  measure (Elem x) = 1

newtype FingerRA f a m = FingerRA (f Size (Elem a) m)

len :: (MonadCredit m, FingerTree f) => FingerRA f a m -> Size
len (FingerRA t) = measure t

splitAt :: (MonadCredit m, FingerTree f) => Int -> FingerRA f a m -> m (FingerRA f a m, FingerRA f a m)
splitAt i (FingerRA xs) = do
   (l, r) <- split (fromIntegral i <) xs
   pure $ (FingerRA l, FingerRA r)

instance FingerTree f => RA.RandomAccess (FingerRA f) where
  empty = pure $ FingerRA empty
  cons x (FingerRA q) = FingerRA <$> cons (Elem x) q
  uncons (FingerRA q) = do
    m <- uncons q
    case m of
      Nothing -> pure Nothing
      Just (Elem x, m') -> do
        pure $ Just (x, FingerRA m')
  lookup i (FingerRA xs) =
    if isEmpty xs
      then pure Nothing
      else do
        Split _ (Elem x) _ <- splitTree (fromIntegral i <) 0 xs
        pure $ Just x
  update i a (FingerRA xs) =
    if isEmpty xs
      then pure $ FingerRA empty
      else do
        Split l (Elem x) r <- splitTree (fromIntegral i <) 0 xs
        if fromIntegral i > len (FingerRA l)
          then FingerRA <$> snoc l (Elem a)
          else FingerRA <$> (concat l =<< cons (Elem a) r)

instance BoundedFingerTree f => RA.BoundedRandomAccess (FingerRA f) where
  qcost n (RA.Cons _) = fcost @f n Cons
  qcost n RA.Uncons = fcostUncons @f n
  qcost n (RA.Lookup i) = fcost @f n SplitTree
  qcost n (RA.Update i _) = fcost @f n SplitTree + max (fcost @f n Snoc) (fcost @f n Cons + fcost @f n Concat)

instance (MonadMemory m, MemoryCell m (f Size (Elem a) m)) => MemoryCell m (FingerRA f a m) where
  prettyCell (FingerRA q) = prettyCell q

instance (MemoryStructure (f Size (Elem a))) => MemoryStructure (FingerRA f a) where
  prettyStructure = prettyStructure

-- Heap

data Prio a = MInfty | Prio a
  deriving (Eq, Ord, Show)

instance Ord a => Semigroup (Prio a) where
  MInfty <> p = p
  p <> MInfty = p
  Prio x <> Prio y = Prio (min x y)

instance Ord a => Monoid (Prio a) where
  mempty = MInfty

instance Ord a => Measured (Elem a) (Prio a) where
  measure (Elem x) = Prio x

newtype FingerHeap f a m = FingerHeap (f (Prio a) (Elem a) m)

instance FingerTree f => H.Heap (FingerHeap f) where
  empty = pure $ FingerHeap empty
  insert x (FingerHeap xs) = FingerHeap <$> cons (Elem x) xs
  merge (FingerHeap a) (FingerHeap b) = FingerHeap <$> concat a b
  splitMin (FingerHeap xs) =
    if isEmpty xs
      then pure Nothing
      else do
        (Split l (Elem x) r) <- splitTree (measure xs >=) MInfty xs
        lr <- concat l r
        pure $ Just (x, FingerHeap lr)

instance BoundedFingerTree f => H.BoundedHeap (FingerHeap f) where
  hcost n (H.Insert _) = fcost @f n Cons
  hcost n H.Merge = fcost @f n Concat
  hcost n H.SplitMin = fcost @f n SplitTree + fcost @f n Concat

instance (MonadMemory m, MemoryCell m (f (Prio a) (Elem a) m)) => MemoryCell m (FingerHeap f a m) where
  prettyCell (FingerHeap q) = prettyCell q

instance (MemoryStructure (f (Prio a) (Elem a))) => MemoryStructure (FingerHeap f a) where
  prettyStructure = prettyStructure

-- Sortable Collection

data Key a = NoKey | Key a
  deriving (Eq, Ord, Show)

instance Semigroup (Key a) where
  k <> NoKey = k
  _ <> k = k

instance Monoid (Key a) where
  mempty = NoKey

instance Eq a => Measured (Elem a) (Key a) where
  measure (Elem x) = Key x

newtype FingerSort f a m = FingerSort (f (Key a) (Elem a) m)

instance FingerTree f => S.Sortable (FingerSort f) where
  empty = pure $ FingerSort empty
  add x (FingerSort xs) = do
    (l, r) <- split (>= Key x) xs
    lxr <- concat l =<< cons (Elem x) r
    pure $ FingerSort lxr
  sort (FingerSort xs) = map (\(Elem x) -> x) <$> treeToList xs

instance BoundedFingerTree f => S.BoundedSortable (FingerSort f) where
  scost n (S.Add _) = fcost @f n SplitTree + fcost @f n Cons + fcost @f n Concat
  scost n S.Sort = fcost @f n TreeToList

instance (MonadMemory m, MemoryCell m (f (Key a) (Elem a) m)) => MemoryCell m (FingerSort f a m) where
  prettyCell (FingerSort q) = prettyCell q

instance (MemoryStructure (f (Key a) (Elem a))) => MemoryStructure (FingerSort f a) where
  prettyStructure = prettyStructure