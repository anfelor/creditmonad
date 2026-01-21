{-# LANGUAGE TypeFamilies, LambdaCase #-}

-- | Gibbons, Jeremy - Moor, Oege de (Eds) - The Fun of Programming
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
  Mrg :: Ord a => SThunk a m -> Skew a m -> SLazyCon m (Skew a m)

instance MonadCredit m => HasStep (SLazyCon m) m where
  step (Mrg a b) = do
    a' <- signedForce a
    mrg a' b

isEmpty :: Skew a m -> Bool
isEmpty Null = True
isEmpty (Fork _ _ _) = False

-- | Force a thunk, paying the debit on good nodes
signedForce :: MonadCredit m => SThunk a m -> m (Skew a m)
signedForce ((s, _), t) = do
  when (s == Good) $ do
    t `creditWith` 1
  force t

size :: Skew a m -> Size
size Null = 0
size (Fork _ ((_, sa), _) ((_, sb), _)) = 1 + sa + sb

sign' :: Skew a m -> Sign
sign' Null = Bad
sign' (Fork _ ((_, sa), _) ((_, sb), _)) = if sa <= sb then Good else Bad

sign :: (MonadCredit m, Ord a) => Thunk m (SLazyCon m) (Skew a m) -> m Sign
sign a = lazymatch a (pure . sign') (\(Mrg a b) -> sign' <$> simMrg a b)

-- | The cost for performing merge on skew heaps:
--   - "log2 (2 * size a)": For our log2 function, log2 1 = log2 0 = 0.
--     We multiply the size by two to ensure that
--     log2 a >= log (a/2) + 1 for all a > 0.
--   - "log2 (2 * size a) + log2 (2 * size b)": each step we reduce
--     one of the arguments, so we need to pay a log for each argument.
--   - "2*(...)": each good node costs two credits,
--     one for the tick and one to pay for the debit.
--   - "alreadyForced": if a good node is at the top level,
--     we have already paid for the debit, but not yet for the tick.
credits :: SThunk a m -> Skew a m -> Credit
credits ((ssa, 0), _) b = isBad (sign' b)
credits ((ssa, sa), _) b = 2 * (log2 sa + log2 (size b)) + 1 + isBad (sign' b)

isBad Good = 0
isBad Bad  = 1

mrg :: (MonadCredit m, Ord a) => Skew a m -> Skew a m -> m (Skew a m)
mrg a Null = tick >> pure a
mrg Null b = tick >> pure b
mrg a@(Fork xa aa ba) b@(Fork xb ab bb)
  | xa <= xb  = join a b
  | otherwise = join b a

join :: (MonadCredit m, Ord a) => Skew a m -> Skew a m -> m (Skew a m)
join (Fork x a b) c = tick >> do
  t <- delay $ Mrg a c
  t `creditWith` credits a c
  sst <- sign t
  pure $ Fork x b ((sst, snd (fst a) + size c), t)

-- | Simulate a merge step: we return the correct result "for free"
simMrg :: (MonadCredit m, Ord a) => SThunk a m -> Skew a m -> m (Skew a m)
simMrg a b = do
  a <- lazymatch (snd a) (\a -> pure a) (\(Mrg a b) -> simMrg a b)
  case (a, b) of
    (a, Null) -> pure a
    (Null, b) -> pure b
    (Fork xa aa ba, Fork xb ab bb)
      | xa <= xb  -> do
        pure $ Fork xa ba ((undefined, snd (fst aa) + size b), undefined)
      | otherwise -> do
        pure $ Fork xb bb ((undefined, snd (fst ab) + size a), undefined)

instance Heap Skew where
  empty = pure Null
  insert x a = do
    null <- ((Bad, 0),) <$> value Null
    a <- ((sign' a, size a),) <$> value a
    t <- delay $ Mrg a (Fork x null null)
    t `creditWith` credits a (Fork x null null)
    sst <- sign t
    signedForce ((sst, snd (fst a) + 1), t)
  merge a b = mrg a b
  splitMin Null = pure Nothing
  splitMin (Fork x a b) = do
    b <- signedForce b
    ab <- delay $ Mrg a b
    ab `creditWith` credits a b
    ssab <- sign ab
    ab <- signedForce ((ssab, snd (fst a) + size b), ab)
    pure $ Just (x, ab)

instance BoundedHeap Skew where
  hcost n (Insert _) = hcost @Skew (n + 1) Merge
  hcost n Merge = 4 * (1 + log2 n)
  hcost n SplitMin = hcost @Skew n Merge

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Skew a m) where
    prettyCell Null = pure $ mkMCell "_" []
    prettyCell (Fork x (_, a) (_, b)) = do
        x' <- prettyCell x
        a' <- prettyCell a
        b' <- prettyCell b
        pure $ mkMCell "" [x', a', b']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (SLazyCon m a) where
  prettyCell (Mrg (_, a) b) = do
    a' <- prettyCell a
    b' <- prettyCell b
    pure $ mkMCell "Mrg" [a', b']

instance Pretty a => MemoryStructure (Skew (PrettyCell a)) where
  prettyStructure = prettyCell