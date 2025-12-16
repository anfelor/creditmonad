{-# LANGUAGE TypeFamilies #-}

-- Gibbons, Jeremy - Moor, Oege de (Eds) - The Fun of Programming
-- Chapter 1 - Fun with binary heap trees - Chris Okasaki
module Test.Credit.Heap.Skew where

import Prettyprinter (Pretty)
import Control.Monad (when)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base
import Test.QuickCheck

data Sign = Good | Bad
  deriving (Eq, Ord, Show)

data Skew a m
  = Null
  | Fork a (SThunk a m) (SThunk a m)

type SThunk a m = ((Sign, Size), Thunk m (SLazyCon m) (Skew a m))
-- ^ we annotate each thunk with its sign and size,
-- this is purely for the purpose of the analysis

data SLazyCon m a where
  Join :: Ord a => Skew a m -> Skew a m -> SLazyCon m (Skew a m)

instance MonadCredit m => HasStep (SLazyCon m) m where
  step (Join a b) = join a b

isEmpty :: Skew a m -> Bool
isEmpty Null = True
isEmpty (Fork _ _ _) = False

-- | The cost for performing merge on skew heaps:
--   - "1 + log2 sa + log2 sb": this is the bound given by Okasaki
--   - "2*": each good node costs two credits, one for the tick
--     and one to pay for the debit
--   - "alreadyForced": if a good node is at the top level,
--     we have already paid for the debit, but not yet for the tick
credits :: (Sign, Size) -> (Sign, Size) -> Credit
credits (ga, sa) (gb, sb) = 2 * (1 + log2 sa + log2 sb) - alreadyForced ga - alreadyForced gb
  where
    alreadyForced Good = 1
    alreadyForced Bad  = 0

size :: Skew a m -> Size
size Null = 0
size (Fork _ ((_, sa), _) ((_, sb), _)) = 1 + sa + sb

sign :: Skew a m -> Sign
sign Null = Bad
sign (Fork _ ((_, sa), _) ((_, sb), _)) = if sa <= sb then Good else Bad

-- | Simulate a join step to report the new size
sjoin :: SThunk a m -> Skew a m -> SThunk a m
sjoin ((_, st), t) b = ((undefined, st + size b), undefined)

-- | Convert a skew heap into a thunk
fromValue :: MonadCredit m => Skew a m -> m (SThunk a m)
fromValue t = ((sign t, size t),) <$> value t

-- | Force a thunk, paying the debit on good nodes
signedForce :: MonadCredit m => SThunk a m -> m (Skew a m)
signedForce ((s, _), t) = do
  when (s == Good) $ do
    t `creditWith` 1
  force t

mrg :: (MonadCredit m, Ord a) => Skew a m -> Skew a m -> m (SThunk a m)
mrg a Null = fromValue a
mrg Null b = fromValue b
mrg a@(Fork xa aa ba) b@(Fork xb ab bb)
  | xa <= xb = do
    t <- delay $ Join a b
    t `creditWith` credits (sign a, size a) (sign b, size b)
    pure ((sign (Fork xa ba (sjoin aa b)), size a + size b), t)
  | otherwise = do
    t <- delay $ Join b a 
    t `creditWith` credits (sign b, size b) (sign a, size a)
    pure ((sign (Fork xb bb (sjoin ab a)), size b + size a), t)

join :: (MonadCredit m, Ord a) => Skew a m -> Skew a m -> m (Skew a m)
join (Fork x a b) c = tick >> do
  a' <- signedForce a
  (s, t) <- mrg a' c
  pure $ Fork x b (s, t)

instance Heap Skew where
  empty = pure Null
  insert x a = do
    null <- fromValue Null
    merge (Fork x null null) a
  merge a b = do 
    (s, t) <- mrg a b
    signedForce (s, t)
  splitMin Null = pure Nothing
  splitMin (Fork x a b) = do
    a <- signedForce a
    b <- signedForce b
    ab <- merge a b
    pure $ Just (x, ab)

instance BoundedHeap Skew where
  hcost n (Insert _) = hcost @Skew (n + 1) Merge
  hcost n Merge = 3 + 4 * log2 n
  hcost n SplitMin = 2 + hcost @Skew n Merge

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Skew a m) where
    prettyCell Null = pure $ mkMCell "_" []
    prettyCell (Fork x (_, a) (_, b)) = do
        x' <- prettyCell x
        a' <- prettyCell a
        b' <- prettyCell b
        pure $ mkMCell "" [x', a', b']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SLazyCon m a) where
  prettyCell (Join a b) = do
    a' <- prettyCell a
    b' <- prettyCell b
    pure $ mkMCell "Join" [a', b']

instance Pretty a => MemoryStructure (Skew (PrettyCell a)) where
  prettyStructure = prettyCell