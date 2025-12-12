{-# LANGUAGE TypeFamilies #-}

-- Gibbons, Jeremy - Moor, Oege de (Eds) - The Fun of Programming
-- Chapter 1 - Fun with binary heap trees - Chris Okasaki
module Test.Credit.Heap.RoundRobin where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

data Colour = Blue | Red
  deriving (Eq, Ord, Show)

data Tree a = Null | Fork Colour a (Tree a) (Tree a)
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
join (Fork Blue x a b) c = tick >> (\ac -> Fork Red x ac b) <$> mrg a c
join (Fork Red x a b) c = tick >> Fork Blue x a <$> mrg b c

newtype RoundRobin a m = RoundRobin (Tree a)

instance Heap RoundRobin where
  empty = pure $ RoundRobin Null
  insert x (RoundRobin a) = do
    RoundRobin <$> mrg (Fork Blue x Null Null) a
  merge (RoundRobin a) (RoundRobin b) = do
    RoundRobin <$> mrg a b
  splitMin (RoundRobin Null) = pure Nothing
  splitMin (RoundRobin (Fork _ x a b)) = do
    Just <$> (x,) <$> RoundRobin <$> mrg a b

instance BoundedHeap RoundRobin where
  hcost n (Insert _) = 2 * log2 (n + 1)
  hcost n Merge = 2 * log2 n
  hcost n SplitMin = 2 * log2 n

instance MemoryCell m a => MemoryCell m (Tree a) where
    prettyCell Null = pure $ mkMCell "Null" []
    prettyCell (Fork n x a b) = do
        n' <- prettyCell $ ShowCell n
        x' <- prettyCell x
        a' <- prettyCell a
        b' <- prettyCell b
        pure $ mkMCell "Fork" [n', x', a', b']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (RoundRobin a m) where
  prettyCell (RoundRobin t) = do
    t' <- prettyCell t
    pure $ mkMCell "RoundRobin" [t']

instance Pretty a => MemoryStructure (RoundRobin (PrettyCell a)) where
  prettyStructure = prettyCell