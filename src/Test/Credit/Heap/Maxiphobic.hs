{-# LANGUAGE TypeFamilies #-}

-- Gibbons, Jeremy - Moor, Oege de (Eds) - The Fun of Programming
-- Chapter 1 - Fun with binary heap trees - Chris Okasaki
module Test.Credit.Heap.Maxiphobic where

import Prettyprinter (Pretty)
import Data.List (sortOn)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

data Tree a = Null | Fork Int a (Tree a) (Tree a)
  deriving (Eq, Ord, Show)

isEmpty :: Tree a -> Bool
isEmpty Null = True
isEmpty (Fork _ _ _ _) = False

mrg :: (MonadCount m, Ord a) => Tree a -> Tree a -> m (Tree a)
mrg a Null = pure a
mrg Null b = pure b
mrg a@(Fork _ xa _ _) b@(Fork _ xb _ _)
  | xa <= xb = join a b
  | otherwise = join b a 

join :: (MonadCount m, Ord a) => Tree a -> Tree a -> m (Tree a)
join (Fork n x a b) c = tick >> Fork (n + size c) x aa <$> mrg bb cc
  where [aa, bb, cc] = reverse $ sortOn size [a, b, c]

size :: Tree a -> Int
size Null = 0
size (Fork n _ _ _) = n

newtype Maxiphobic a m = Maxiphobic (Tree a)

instance Heap Maxiphobic where
  empty = pure $ Maxiphobic Null
  insert x (Maxiphobic a) = do
    Maxiphobic <$> mrg (Fork 1 x Null Null) a
  merge (Maxiphobic a) (Maxiphobic b) = do
    Maxiphobic <$> mrg a b
  splitMin (Maxiphobic Null) = pure Nothing
  splitMin (Maxiphobic (Fork _ x a b)) = do
    Just <$> (x,) <$> Maxiphobic <$> mrg a b

instance BoundedHeap Maxiphobic where
  hcost n (Insert _) = 2 * log2 (n + 1)
  hcost n Merge = 2 * log2 n
  hcost n SplitMin = 2 * log2 n

instance MemoryCell m a => MemoryCell m (Tree a) where
    prettyCell Null = pure $ mkMCell "Null" []
    prettyCell (Fork n x a b) = do
        n' <- prettyCell n
        x' <- prettyCell x
        a' <- prettyCell a
        b' <- prettyCell b
        pure $ mkMCell "Fork" [n', x', a', b']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Maxiphobic a m) where
  prettyCell (Maxiphobic t) = do
    t' <- prettyCell t
    pure $ mkMCell "Maxiphobic" [t']

instance Pretty a => MemoryStructure (Maxiphobic (PrettyCell a)) where
  prettyStructure = prettyCell