{-# LANGUAGE GADTs #-}

module Test.Credit.Sortable.MergeSort where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Sortable.Base

data MergeSort a m = MergeSort Size (Thunk m (MLazyCon m) [[a]])

mrg :: MonadCredit m => Ord a => [a] -> [a] -> m [a]
mrg [] ys = pure ys
mrg xs [] = pure xs
mrg (x:xs) (y:ys) = tick >>
  if x <= y
    then (x:) <$> mrg xs (y:ys)
    else (y:) <$> mrg (x:xs) ys

addSeg :: MonadCredit m => Ord a => [a] -> [[a]] -> Size -> m [[a]]
addSeg seg segs size =
  if size `mod` 2 == 0 then pure $ seg : segs
  else do -- technically we should have a tick here, but Okasaki doesn't and we follow his presentation
    let (seg1:segs') = segs
    seg' <- mrg seg seg1 
    addSeg seg' segs' (size `div` 2)

psi :: Size -> Credit
psi n = 2 * linear n - 2 * sum [ linear $ b i * (n `mod` 2^i + 1) | i <- [0..(log2 n + 1)] ]
  where
    b i = (n `div` 2^i) `mod` 2

data MLazyCon m a where
  Empty :: MLazyCon m [[a]]
  AddSeg :: Ord a => [a] -> Thunk m (MLazyCon m) [[a]] -> Size -> MLazyCon m [[a]]

instance MonadCredit m => HasStep (MLazyCon m) m where
  step Empty = pure []
  step (AddSeg seg segs size) = do
    creditWith segs (psi size)
    segs' <- force segs
    addSeg seg segs' size

mrgAll :: MonadCredit m => Ord a => [a] -> [[a]] -> m [a]
mrgAll xs [] = pure xs
mrgAll xs (seg:segs) = tick >> do
  seg' <- mrg xs seg
  mrgAll seg' segs

instance Sortable MergeSort where
  empty = do
    segs <- delay Empty
    pure $ MergeSort 0 segs
  add x (MergeSort size segs) = do
    segs' <- delay $ AddSeg [x] segs size
    creditWith segs' (2 * log2 size + 1)
    pure $ MergeSort (size + 1) segs'
  sort (MergeSort size segs) = do
    creditWith segs (psi size)
    segs' <- force segs
    mrgAll [] segs'

instance BoundedSortable MergeSort where
  scost n (Add _) = 2 * log2 n + 1
  scost n Sort = psi n +  2 * linear n

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (MLazyCon m a) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (AddSeg seg segs size) = do
    -- seg' <- prettyCell seg
    segs' <- prettyCell segs
    size' <- prettyCell size
    pure $ mkMCell "AddSeg" [segs', size']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (MergeSort a m) where
  prettyCell (MergeSort size segs) = do
    size' <- prettyCell size
    segs' <- prettyCell segs
    pure $ mkMCell "MergeSort" [size', segs']

instance Pretty a => MemoryStructure (MergeSort (PrettyCell a)) where
  prettyStructure = prettyCell