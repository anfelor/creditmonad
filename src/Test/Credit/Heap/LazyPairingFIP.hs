{-# LANGUAGE GADTs #-}

module Test.Credit.Heap.LazyPairingFIP where

import Prettyprinter (Pretty)

import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

-- Fully in-place version of Okasaki's lazy pairing heaps.
-- The split of 'Link' into 'Pairing' and 'Assembly' follows
-- 'Amortized Complexity Verified' (2019) by Nipkow and Brinkop, Section 8.

data SingleRoot a m
  = NeedsPair (LazyPairingFIP a m) -- padded to three elements
  | AllPaired

data LazyPairingFIP a m
  = Empty
  | Heap a (SingleRoot a m) (PThunk m (LazyPairingFIP a m))

-- | In Koka, we can omit the size -- it is only needed for the analysis
type PThunk m a = (Size, Thunk m (PLazyCon m) a)

-- | Invariant: For 'Heap x a (sm, m)', we have either:
--   - 'a' is Empty and 'm' has (2 * log2 sm) credits
--   - 'a' is not Empty and 'm' has (4 * log2 sm) credits
--   - Right before forcing, 'm' has (6 * log2 sm) credits
heap :: MonadCredit m => a -> SingleRoot a m -> PThunk m (LazyPairingFIP a m) -> m (LazyPairingFIP a m)
heap x AllPaired (sm, m) = do
  m `hasAtLeast` (2 * log2 sm)
  pure $ Heap x AllPaired (sm, m)
heap x a (sm, m) = do
  m `hasAtLeast` (4 * log2 sm)
  pure $ Heap x a (sm, m)

size :: LazyPairingFIP a s -> Size
size Empty = 0
size (Heap _ AllPaired (sm, _)) = 1 + sm
size (Heap _ (NeedsPair a) (sm, _)) = 1 + sm + size a

data PLazyCon m a where
  Pairing :: Ord a => LazyPairingFIP a m -> LazyPairingFIP a m -> PLazyCon m (LazyPairingFIP a m)
  -- ^ Merging 'h = Pairing(a, b)' costs one tick and performs one link.
  --   Because 'link a b' costs '2 * log2 (sa + sb)' credits, we have total costs of:
  --     1 + 2*log2 (sa + sb)
  Assembly :: Ord a => PThunk m (LazyPairingFIP a m) -> PThunk m (LazyPairingFIP a m) -> PLazyCon m (LazyPairingFIP a m)
  -- ^ Merging 'h = Assembly(ab, m)' costs two tick and performs one link, and assigns some credits to 'ab' and 'm'.
  --   Because 'link a b' costs '2 * log2 (sa + sb)' credits, we have total costs of:
  --     2 + 2*log2 (sa + sb + sm) + 2*log2 (sa + sb) + 2*log2 sm
  --     <= 6 * log2 sh (since sa + sb + sm <= sh)

instance MonadCredit m => HasStep (PLazyCon m) m where
  step (Pairing a b) = tick >> link a b -- 1 + 2 * log2 (sa + sb)
  step (Assembly (sab, ab) (sm, m)) = tick >> do -- 1
    m  `creditWith` (2 * log2 sm) -- 2 * log2 sm
    ab `creditWith` (1 + 2 * log2 sab) -- 1 + 2 * log2 sab
    ab <- force ab
    m  <- force m
    link ab m -- 2 * log2 (sa + sb + sm)

data NEHeap m a = NEHeap a (SingleRoot a m) (PThunk m (LazyPairingFIP a m))

-- | 'mergePairs' costs up to 'log2 (sz + sa)' credits
-- To be fip, we need to pass a size-3 space credit
mergePairs :: MonadCredit m => Ord a => NEHeap m a -> LazyPairingFIP a m -> m (LazyPairingFIP a m)
mergePairs (NEHeap x AllPaired (sm, m)) a = do
  m `creditWith` (2 * log2 sm)
  heap x (NeedsPair a) (sm, m)
mergePairs (NEHeap x (NeedsPair b) (sm, m)) a = do
  ab <- delay $ Pairing a b
  t  <- delay $ Assembly (size a + size b, ab) (sm, m)
  let sz = size a + size b + sm
  t `creditWith` (2 * log2 sz)
  heap x AllPaired (sz, t)

-- | 'link' costs up to 'log2 (sz + sa)' credits
-- To be fip, we need to pass a size-3 space credit
link :: MonadCredit m => Ord a => LazyPairingFIP a m -> LazyPairingFIP a m -> m (LazyPairingFIP a m)
link a Empty = pure a
link Empty b = pure b
link a@(Heap x a1 a2) b@(Heap y b1 b2)
  | x <= y    = mergePairs (NEHeap x a1 a2) b
  | otherwise = mergePairs (NEHeap y b1 b2) a 

instance Heap LazyPairingFIP where
  empty = pure Empty
  insert x a = do
    t <- value Empty
    merge (Heap x AllPaired (0, t)) a
  -- | 'merge' costs '1 + log2 (sa + sb)' credits
  merge a b = tick >> link a b
  splitMin Empty = pure Nothing
  splitMin (Heap x a (sm, m)) = do
    m `creditWith` (4 * log2 sm) -- in case 'a' is Empty
    m  <- force m
    am <- case a of
        NeedsPair a -> merge a m
        AllPaired -> pure m
    pure $ Just (x, am)

instance BoundedHeap LazyPairingFIP where
  hcost n (Insert _) = 1 + 2 * log2 (n + 1)
  hcost n Merge = 1 + 2 * log2 (n + 1)
  hcost n SplitMin = 1 + 6 * log2 (n + 1)

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (PLazyCon m a) where
  prettyCell (Pairing a b) = do
    a' <- prettyCell a
    b' <- prettyCell b
    pure $ mkMCell "Pairing" [a', b']
  prettyCell (Assembly ab m) = do
    ab' <- prettyCell ab
    m' <- prettyCell m
    pure $ mkMCell "Assembly" [ab', m']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SingleRoot a m) where
  prettyCell AllPaired = pure $ mkMCell "None" []
  prettyCell (NeedsPair a) = do
    a' <- prettyCell a
    pure $ a'

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (LazyPairingFIP a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Heap x a m) = do
    x' <- prettyCell x
    a' <- prettyCell a
    m' <- prettyCell m
    pure $ mkMCell "Heap" [x', a', m']

instance Pretty a => MemoryStructure (LazyPairingFIP (PrettyCell a)) where
  prettyStructure = prettyCell