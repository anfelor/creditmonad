{-# LANGUAGE GADTs #-}

module Test.Credit.Queue.Bootstrapped where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Queue.Base

rev :: MonadCredit m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc) 

data BLazyCon m a where
  Rev :: [a] -> BLazyCon m [a]

instance MonadCredit m => HasStep (BLazyCon m) m where
  step (Rev xs) = rev xs []

type BThunk m = Thunk m (BLazyCon m)

data NEQueue a m = NEQueue
  { lenfm :: !Int
  , f :: [a]
  , m :: Bootstrapped (BThunk m [a]) m
  , ghost :: BThunk m [a]
  , lenr :: !Int
  , r :: [a]
  }

data Bootstrapped a m = Empty | BQueue (NEQueue a m)

checkQ :: MonadCredit m => NEQueue a m -> m (Bootstrapped a m)
checkQ q@(NEQueue lenfm f m _ lenr r)
  | lenr <= lenfm = checkF q
  | otherwise = do
    r' <- delay $ Rev r
    creditWith r' 2
    m' <- snoc' m r'
    checkF (NEQueue (lenfm + lenr) f m' r' 0 [])

checkF :: MonadCredit m => NEQueue a m -> m (Bootstrapped a m)
checkF (NEQueue lenfm [] Empty _ lenr r) = pure Empty
checkF (NEQueue lenfm [] (BQueue m) ghost lenr r) = do
  (f, m') <- uncons'' m
  f' <- force f
  pure $ BQueue (NEQueue lenfm f' m' ghost lenr r)
checkF q = pure $ BQueue q

snoc' :: MonadCredit m => Bootstrapped a m -> a -> m (Bootstrapped a m)  
snoc' Empty x = do
  ghost <- delay $ Rev undefined -- never forced
  pure $ BQueue (NEQueue 1 [x] Empty ghost 0 [])
snoc' (BQueue (NEQueue lenfm f m g lenr r)) x = do
  creditWith g 1
  checkQ (NEQueue lenfm f m g (lenr + 1) (x : r))

uncons'' :: MonadCredit m => NEQueue a m -> m (a, Bootstrapped a m)
uncons'' (NEQueue lenfm (x : f') m g lenr r) = tick >> do
  creditWith g 1
  q <- checkQ (NEQueue (lenfm - 1) f' m g lenr r)
  pure (x, q)

uncons' :: MonadCredit m => Bootstrapped a m -> m (Maybe (a, Bootstrapped a m))
uncons' Empty = pure Nothing
uncons' (BQueue ne) = Just <$> uncons'' ne

instance Queue Bootstrapped where
  empty = pure Empty
  snoc q x = snoc' q x
  uncons q = uncons' q

instance BoundedQueue Bootstrapped where
  qcost n (Snoc _) = 3 * (max 1 (logstar n))
  qcost n Uncons = 6 * (max 1 (logstar n))

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (BLazyCon m a) where
  prettyCell (Rev xs) = do
    xs' <- prettyCell xs
    pure $ mkMCell "Rev" [xs']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Bootstrapped a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (BQueue (NEQueue lenfm f m _ lenr r)) = do
    lenfm' <- prettyCell lenfm
    f' <- prettyCell f
    m' <- prettyCell m
    lenr' <- prettyCell lenr
    r' <- prettyCell r
    pure $ mkMCell "Queue" [lenfm', f', m', lenr', r']

instance Pretty a => MemoryStructure (Bootstrapped (PrettyCell a)) where
  prettyStructure = prettyCell