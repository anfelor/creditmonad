{-# LANGUAGE TypeFamilies #-}

module Test.Credit.Queue.Physicists where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Queue.Base

app :: MonadCredit m => [a] -> [a] -> m [a]
app [] ys = pure ys
app (x : xs) ys = tick >> app xs (x : ys)

rev :: MonadCredit m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc)

data PLazyCon m a where
  Empty :: PLazyCon m [a]
  AppRev :: [a] -> [a] -> PLazyCon m [a]
  Tail :: Thunk m (PLazyCon m) [a] -> PLazyCon m [a]

instance MonadCredit m => HasStep (PLazyCon m) m where
  step Empty = pure []
  step (AppRev xs ys) = app xs =<< rev ys []
  step (Tail xs) = tick >> drop 1 <$> force xs

type PThunk m = Thunk m (PLazyCon m)

data Physicists a m = Queue [a] Int (PThunk m [a]) (PThunk m [a]) Int [a]

checkw :: MonadCredit m => Physicists a m -> m (Physicists a m)
checkw (Queue working lenf front ghost lenr rear) = case working of
  [] -> do
    front' <- force front
    pure $ Queue front' lenf front ghost lenr rear
  _ -> pure $ Queue working lenf front ghost lenr rear

check :: MonadCredit m => Physicists a m -> m (Physicists a m)
check q@(Queue _ lenf front ghost lenr rear) =
  if lenr <= lenf
    then do
      creditWith ghost 1
      checkw q
    else do
      working <- force front
      front' <- delay $ AppRev working rear
      creditWith front' 1
      checkw $ Queue working (lenf + lenr) front' front' 0 []

instance Queue Physicists where
  empty = do
    front <- delay Empty
    pure $ Queue [] 0 front front 0 []
  snoc (Queue working lenf front ghost lenr rear) x = tick >> do
    creditWith ghost 1
    check (Queue working lenf front ghost (lenr + 1) (x : rear))
  uncons (Queue [] lenf front ghost lenr rear) = tick >> pure Nothing
  uncons (Queue (x : working) lenf front ghost lenr rear) = tick >> do
    front' <- delay $ Tail front
    creditWith front' 1
    creditWith ghost 1
    q' <- check $ Queue working (lenf - 1) front' ghost lenr rear
    pure $ Just (x, q')

instance BoundedQueue Physicists where
  qcost _ (Snoc _) = 3
  qcost _ Uncons = 4

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (PLazyCon m a) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (AppRev xs ys) = do
    xs' <- prettyCell xs
    ys' <- prettyCell ys
    pure $ mkMCell "AppRev" [xs', ys']
  prettyCell (Tail xs) = do
    xs' <- prettyCell xs
    pure $ mkMCell "Tail" [xs']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Physicists a m) where
  prettyCell (Queue working lenf front _ lenr rear) = do
    working' <- prettyCell working
    lenf' <- prettyCell lenf
    front' <- prettyCell front
    lenr' <- prettyCell lenr
    rear' <- prettyCell rear
    pure $ mkMCell "Queue" [working', lenf', front', lenr', rear']

instance Pretty a => MemoryStructure (Physicists (PrettyCell a)) where
  prettyStructure = prettyCell