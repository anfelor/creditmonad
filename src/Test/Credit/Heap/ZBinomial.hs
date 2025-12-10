{-# LANGUAGE TypeFamilies #-}

-- Binomial Heaps with explicit Zeroes
-- similar to scheduled Binomial Heaps
module Test.Credit.Heap.ZBinomial where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

data Tree a = Node a [Tree a]
  deriving (Eq, Ord, Show)

data Digit a = Zero | One (Tree a)
  deriving (Eq, Ord, Show)

root :: Tree a -> a
root (Node x _) = x

rev :: MonadCredit m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc)

link :: Ord a => Tree a -> Tree a -> Tree a
link t1@(Node x1 c1) t2@(Node x2 c2)
  | x1 <= x2 = Node x1 (t2:c1)
  | otherwise = Node x2 (t1:c2)

insTree :: MonadCredit m => Ord a => Tree a -> [Digit a] -> m [Digit a]
insTree t [] = pure [One t]
insTree t (Zero   : ts) = pure $ One t : ts
insTree t (One t' : ts) = tick >> (Zero:) <$> insTree (link t t') ts

mrg :: MonadCredit m => Ord a => [Digit a] -> [Digit a] -> m [Digit a]
mrg ts1 [] = pure ts1
mrg [] ts2 = pure ts2
mrg (Zero  :ts1) (Zero  :ts2) = tick >> (Zero:) <$> mrg ts1 ts2
mrg (One t1:ts1) (Zero  :ts2) = tick >> (One t1:) <$> mrg ts1 ts2
mrg (Zero  :ts1) (One t2:ts2) = tick >> (One t2:) <$> mrg ts1 ts2
mrg (One t1:ts1) (One t2:ts2) = do
  tick
  m <- mrg ts1 ts2
  i <- insTree (link t1 t2) m
  pure $ Zero : i

removeMinTree :: MonadCredit m => Ord a => [Digit a] -> m (Tree a, [Digit a])
removeMinTree [] = error "removeMinTree"
removeMinTree [One t] = pure (t, [])
removeMinTree (Zero:ts) = tick >> do
  (t', ts') <- removeMinTree ts
  pure $ (t', Zero:ts')
removeMinTree (One t:ts) = tick >> do
  (t', ts') <- removeMinTree ts
  pure $ if root t <= root t' then (t, Zero:ts) else (t', One t:ts')

data ZBinomial a m = ZBinomial Size (Thunk m (Lazy m) [Digit a])

allZeros :: Size -> Credit
allZeros 0 = 0
allZeros n = (fromIntegral $ (n + 1) `mod` 2) + allZeros (n `div` 2)

instance Heap ZBinomial where
  empty = do
    t <- delay $ Lazy $ pure []
    pure $ ZBinomial 0 t
  insert x (ZBinomial n h) = do
    ts <- delay $ Lazy $ do 
      creditWith h (allZeros n)
      h' <- force h
      insTree (Node x []) h'
    creditWith ts 2
    pure $ ZBinomial (n + 1) ts
  merge (ZBinomial n1 t1) (ZBinomial n2 t2) = do
    t1 `creditWith` (allZeros n1)
    ts1 <- force t1
    t2 `creditWith` (allZeros n2)
    ts2 <- force t2
    ts <- value =<< mrg ts1 ts2
    pure $ ZBinomial (n1 + n2) ts
  splitMin (ZBinomial n t) = do
    creditWith t (log2 n)
    ts <- force t
    case ts of
      [] -> pure Nothing
      _ -> do
        (Node x ts1, ts2) <- removeMinTree ts
        t' <- delay $ Lazy $ do
          rts1 <- rev (map One ts1) []
          mrg rts1 ts2
        creditWith t' (2 * log2 n)
        pure $ Just (x, ZBinomial (max 0 (n - 1)) t')

instance BoundedHeap ZBinomial where
  hcost _ (Insert _) = 2
  hcost n Merge = 3 * log2 n
  hcost n SplitMin = 4 * log2 n

instance MemoryCell m a => MemoryCell m (Tree a) where
  prettyCell (Node x c) = do
    x' <- prettyCell x
    c' <- mapM prettyCell c
    pure $ mkMCell "Node" [x', mkMList c' Nothing]

instance MemoryCell m a => MemoryCell m (Digit a) where
  prettyCell Zero = pure $ mkMCell "Zero" []
  prettyCell (One t) = do
    t' <- prettyCell t
    pure $ mkMCell "One" [t']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (ZBinomial a m) where
  prettyCell (ZBinomial _ t) = do
    t' <- prettyCell t
    pure $ mkMCell "ZBinomial" [t']

instance Pretty a => MemoryStructure (ZBinomial (PrettyCell a)) where
  prettyStructure = prettyCell