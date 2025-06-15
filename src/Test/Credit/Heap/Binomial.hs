{-# LANGUAGE TypeFamilies #-}

module Test.Credit.Heap.Binomial where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

data Tree a = Node Int a [Tree a]
  deriving (Eq, Ord, Show)

rank :: Tree a -> Int
rank (Node r _ _) = r

root :: Tree a -> a
root (Node _ x _) = x

rev :: MonadCredit m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc)

link :: Ord a => Tree a -> Tree a -> Tree a
link t1@(Node r x1 c1) t2@(Node _ x2 c2)
  | x1 <= x2 = Node (r+1) x1 (t2:c1)
  | otherwise = Node (r+1) x2 (t1:c2)

insTree :: MonadCredit m => Ord a => Tree a -> [Tree a] -> m [Tree a]
insTree t [] = pure [t]
insTree t ts@(t':ts')
  | rank t < rank t' = pure $ t:ts
  | otherwise = tick >> insTree (link t t') ts'

mrg :: MonadCredit m => Ord a => [Tree a] -> [Tree a] -> m [Tree a]
mrg ts1 [] = pure ts1
mrg [] ts2 = pure ts2
mrg ts1@(t1:ts1') ts2@(t2:ts2')
  | rank t1 < rank t2 = tick >> (t1 :) <$> mrg ts1' ts2
  | rank t2 < rank t1 = tick >> (t2 :) <$> mrg ts1 ts2'
  | otherwise = tick >> do
    insTree (link t1 t2) =<< mrg ts1' ts2'

removeMinTree :: MonadCredit m => Ord a => [Tree a] -> m (Tree a, [Tree a])
removeMinTree [] = error "removeMinTree"
removeMinTree [t] = pure (t, [])
removeMinTree (t:ts) = tick >> do
  (t', ts') <- removeMinTree ts
  pure $ if root t <= root t' then (t, ts) else (t', t:ts')

data Binomial a m = Binomial Size (Thunk m (Lazy m) [Tree a])

allZeros :: Size -> Credit
allZeros 0 = 0
allZeros n = (fromIntegral $ (n + 1) `mod` 2) + allZeros (n `div` 2)

instance Heap Binomial where
  empty = do
    t <- delay $ Lazy $ pure []
    pure $ Binomial 0 t
  insert x (Binomial n h) = do
    ts <- delay $ Lazy $ do 
      creditWith h (allZeros n)
      h' <- force h
      insTree (Node 0 x []) h'
    creditWith ts 2
    pure $ Binomial (n + 1) ts
  merge (Binomial n1 t1) (Binomial n2 t2) = do
    t1 `creditWith` (allZeros n1)
    ts1 <- force t1
    t2 `creditWith` (allZeros n2)
    ts2 <- force t2
    ts <- delay $ Lazy $ mrg ts1 ts2
    ts `creditWith` (log2 (n1 + n2))
    pure $ Binomial (n1 + n2) ts
  splitMin (Binomial n t) = do
    creditWith t (log2 n)
    ts <- force t
    case ts of
      [] -> pure Nothing
      _ -> do
        (Node _ x ts1, ts2) <- removeMinTree ts
        t' <- delay $ Lazy $ do
          rts1 <- rev ts1 []
          mrg rts1 ts2
        creditWith t' (2 * log2 n)
        pure $ Just (x, Binomial (max 0 (n - 1)) t')

instance BoundedHeap Binomial where
  hcost _ (Insert _) = 2
  hcost n Merge = 3 * log2 n
  hcost n SplitMin = 4 * log2 n

instance MemoryCell m a => MemoryCell m (Tree a) where
  prettyCell (Node r x c) = do
    r' <- prettyCell r
    x' <- prettyCell x
    c' <- mapM prettyCell c
    pure $ mkMCell "Node" [r', x', mkMList c' Nothing]

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Binomial a m) where
  prettyCell (Binomial _ t) = do
    t' <- prettyCell t
    pure $ mkMCell "Binomial" [t']

instance Pretty a => MemoryStructure (Binomial (PrettyCell a)) where
  prettyStructure = prettyCell