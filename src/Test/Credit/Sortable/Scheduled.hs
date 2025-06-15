{-# LANGUAGE GADTs #-}

module Test.Credit.Sortable.Scheduled where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Sortable.Base

rev :: MonadCredit m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc)

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

streamToList :: MonadCredit m => Stream m a -> m [a]
streamToList xs = smatch xs
  (pure [])
  (\x xs' -> (x:) <$> streamToList xs')

type Schedule m a = [Stream m a]

data SMergeSort a m = SMergeSort Size [(Stream m a, Schedule m a)]

mrg :: MonadCredit m => Ord a => Stream m a -> Stream m a -> m (Stream m a)
mrg xs ys = indirect $ do
  smatch xs (pure ys) $ \x xs' ->
    smatch ys (pure xs) $ \y ys' -> do
      if x <= y
        then (SCons x) <$> mrg xs' ys
        else (SCons y) <$> mrg xs ys'

exec1 :: MonadCredit m => Schedule m a -> m (Schedule m a)
exec1 [] = pure []
exec1 (ds:sched) = credit 2 ds >> smatch ds
  (exec1 sched)
  (\_ xs -> pure $ xs : sched)

exec2 :: MonadCredit m => (Stream m a, Schedule m a) -> m (Stream m a, Schedule m a)
exec2 (xs, sched) = exec1 sched >>= exec1 >>= pure . (xs,)

execAll :: MonadCredit m => Schedule m a -> m ()
execAll [] = pure ()
execAll sched = exec1 sched >>= execAll

addSeg :: MonadCredit m => Ord a => Stream m a -> [(Stream m a, Schedule m a)] -> Size -> Schedule m a -> m [(Stream m a, Schedule m a)]
addSeg xs segs size rsched =
  if size `mod` 2 == 0
    then do
      sched <- rev rsched [] -- log2 size
      pure $ (xs, sched) : segs
    else do
      let ((xs', []) : segs') = segs
      xs'' <- mrg xs xs'
      addSeg xs'' segs' (size `div` 2) (xs'' : rsched)

mrgAll :: MonadCredit m => Ord a => Stream m a -> [(Stream m a, Schedule m a)] -> m (Stream m a)
mrgAll xs [] = pure xs
mrgAll xs ((xs', sched):segs) = do
  execAll sched -- total cost: 3 * linear size
  seg <- mrg xs xs'
  execAll [seg] -- total cost: 6 * linear size
  mrgAll seg segs

instance Sortable SMergeSort where
  empty = pure $ SMergeSort 0 []
  add x (SMergeSort size segs) = do
    segs' <- addSeg (SCons x SNil) segs size [] -- 1 * (log2 size + 1)
    segs'' <- mapM exec2 segs' -- 6 * (log2 size + 1)
    pure $ SMergeSort (size + 1) segs''
  sort (SMergeSort size segs) = do
    s <- mrgAll SNil segs -- 9 * (log2 size + 1)
    streamToList s -- linear size

instance BoundedSortable SMergeSort where
  scost n (Add _) = 7 * (log2 n + 1)
  scost n Sort = 10 * (linear n + 1)

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Stream m a) where
  prettyCell xs = mkMList <$> toList xs <*> toHole xs
    where
      toList SNil = pure $ []
      toList (SCons x xs) = (:) <$> prettyCell x <*> toList xs
      toList (SIndirect t) = pure $ []

      toHole SNil = pure $ Nothing
      toHole (SCons x xs) = toHole xs
      toHole (SIndirect t) = Just <$> prettyCell t

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SMergeSort a m) where
  prettyCell (SMergeSort size segs) = do
    size' <- prettyCell size
    segs' <- prettyCell segs
    pure $ mkMCell "SMergeSort" [size', segs']

instance Pretty a => MemoryStructure (SMergeSort (PrettyCell a)) where
  prettyStructure = prettyCell