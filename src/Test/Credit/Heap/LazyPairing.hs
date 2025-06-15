{-# LANGUAGE GADTs #-}

module Test.Credit.Heap.LazyPairing where

import Prettyprinter (Pretty)

import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

-- Okasaki does not present an amortized analysis and instead merely conjectures
-- that they have O(log n) amortized cost for insert and splitMin (Section 6.5).
-- An amortized analysis in a sequential setting is given by Nipkow and Brinkop
-- in 'Amortized Complexity Verified' (2019), Section 8.
-- Below we generalize it to the persistent setting.

data LazyPairing a s
  = Empty
  | Heap Size a (LazyPairing a s) (PThunk s (LazyPairing a s))
  -- ^ Changed from Okasaki is that we annotate the size of the thunk.
  --   Invariant: For 'Heap sm x a m', we have either:
  --   - 'a' is Empty and 'm' has (log2 sm) credits
  --   - 'a' is not Empty and 'm' has (2 * log2 sm) credits
  --   - Right before forcing, 'm' has (3 * log2 sm) credits

size :: LazyPairing a s -> Size
size Empty = 0
size (Heap sm _ a _) = 1 + sm + size a

data PLazyCon m a where
  Em :: PLazyCon m (LazyPairing a m)
  Link :: Ord a => Size -> LazyPairing a m -> LazyPairing a m -> Thunk m (PLazyCon m) (LazyPairing a m) -> PLazyCon m (LazyPairing a m)
  -- ^ Merging 'h = Link(a, b, m)' costs one tick and performs two links, and assigns some credits to 'm'.
  --   Because 'link a b' costs 'log2 (sa + sb)' credits, we have total costs of:
  --     2 + 2*log2 (sa + sb + sm) + 2*log2 (sa + sb) + 2*log2 sm
  --     <= 6 * log2 sh (since sa + sb + sm <= sh)

instance MonadCredit m => HasStep (PLazyCon m) m where
  step Em = pure Empty
  step (Link sm a b m) = tick >> do -- 1
    creditWith m (log2 sm) -- log2 sm
    m <- force m -- free
    ab <- link a b -- log2 (sa + sb)
    link ab m -- log2 (sa + sb + sm)

type PThunk s = Thunk s (PLazyCon s)

data NEHeap s a = NEHeap Size a (LazyPairing a s) (PThunk s (LazyPairing a s))

-- | 'mergePairs' costs up to 'log2 (sz + sa)' credits
mergePairs :: MonadCredit m => Ord a => NEHeap m a -> LazyPairing a m -> m (LazyPairing a m)
mergePairs (NEHeap sm x Empty m) a = do
  creditWith m (log2 sm)
  pure $ Heap sm x a m
mergePairs (NEHeap sm x b m) a = do
  t <- delay $ Link sm a b m
  let sz = size a + size b + sm
  creditWith t (log2 sz)
  pure $ Heap sz x Empty t

-- | 'link' costs up to 'log2 (sz + sa) + 1' credits
link :: MonadCredit m => Ord a => LazyPairing a m -> LazyPairing a m -> m (LazyPairing a m)
link a Empty = pure a
link Empty b = pure b
link a@(Heap sa x a1 a2) b@(Heap sb y b1 b2)
  | x <= y    = mergePairs (NEHeap sa x a1 a2) b
  | otherwise = mergePairs (NEHeap sb y b1 b2) a 

instance Heap LazyPairing where
  empty = pure Empty
  insert x a = do
    t <- delay $ Em
    merge (Heap 0 x Empty t) a
  -- | 'merge' costs '1 + log2 (sa + sb)' credits
  merge a b = tick >> link a b
  splitMin Empty = pure Nothing
  splitMin (Heap sm x a m) = do
    creditWith m (2 * log2 sm) -- in case 'a' is Empty
    m <- force m
    am <- merge a m
    pure $ Just (x, am)

instance BoundedHeap LazyPairing where
  hcost n (Insert _) = 1 + log2 (n + 1)
  hcost n Merge = 1 + log2 (n + 1)
  hcost n SplitMin = 1 + 3 * log2 (n + 1)

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (PLazyCon m a) where
  prettyCell Em = pure $ mkMCell "Empty" []
  prettyCell (Link _ a b m) = do
    a' <- prettyCell a
    b' <- prettyCell b
    m' <- prettyCell m
    pure $ mkMCell "Link" [a', b', m']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (LazyPairing a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Heap sz x a m) = do
    sz' <- prettyCell sz
    x' <- prettyCell x
    a' <- prettyCell a
    m' <- prettyCell m
    pure $ mkMCell "Heap" [sz', x', a', m']

instance Pretty a => MemoryStructure (LazyPairing (PrettyCell a)) where
  prettyStructure = prettyCell