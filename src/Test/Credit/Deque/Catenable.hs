{-# LANGUAGE GADTs, LambdaCase #-}

module Test.Credit.Deque.Catenable where

import Prelude hiding (concat)
import Prettyprinter (Pretty)
import Control.Monad
import Control.Monad.Credit
import Test.Credit.Deque.Base
import qualified Test.Credit.Queue.Base as Q
import qualified Test.Credit.Queue.Basic as Q

-- | A rose tree where the elements are pre-ordered
data CatDeque a m
  = E
  | C a -- ^ head
      (Q.BasicQueue (Thunk m (CLazyCon m) (CatDeque a m)) m) -- ^ tail

data CLazyCon m a where
  Force :: Thunk m (CLazyCon m) (CatDeque a m) -> CLazyCon m (CatDeque a m)
  LinkAll :: Q.BasicQueue (Thunk m (CLazyCon m) (CatDeque a m)) m -> CLazyCon m (CatDeque a m)

instance MonadInherit m => HasStep (CLazyCon m) m where
  step (Force t) = force t
  step (LinkAll q) = linkAll q

costSnoc :: Credit
costSnoc = Q.qcost @(Q.BasicQueue) undefined (Q.Snoc undefined)

costUncons :: Credit
costUncons = Q.qcost @(Q.BasicQueue) undefined (Q.Uncons)

link :: MonadInherit m => CatDeque a m -> Thunk m (CLazyCon m) (CatDeque a m) -> m (CatDeque a m)
link (C x q) s = C x <$> Q.snoc q s

linkAll :: MonadInherit m => Q.BasicQueue (Thunk m (CLazyCon m) (CatDeque a m)) m -> m (CatDeque a m)
linkAll q = do
  m <- Q.uncons q
  case m of
    Nothing -> fail "linkAll: empty queue"
    Just (t, q') -> do
      t <- force t
      if Q.isEmpty q' then pure t
      else do
        if Q.size q' == 1
          then do
            (Just (t', _)) <- Q.uncons q'
            s <- delay $ Force t'
            link t s
          else do
            s <- delay $ LinkAll q'
            creditWith s costUncons -- for the last uncons
            link t s

linkTop :: MonadInherit m => Q.BasicQueue (Thunk m (CLazyCon m) (CatDeque a m)) m -> m (CatDeque a m)
linkTop q = do
  m <- Q.uncons q
  case m of
    Nothing -> fail "linkAll: empty queue"
    Just (t, q') -> do
      dischargeThunk t
      t1 <- force t
      if Q.isEmpty q' then pure t1
      else do
        if Q.size q' == 1
          then do
            (Just (t', _)) <- Q.uncons q'
            s <- delay $ Force t'
            link t1 s
          else do
            s <- delay $ LinkAll q'
            creditWith s costUncons -- for the last uncons
            -- creditWith s (costSnoc + costUncons)
            dischargeThunk s
            link t1 s

concat' :: MonadInherit m => CatDeque a m -> CatDeque a m -> m (CatDeque a m)
concat' E xs = pure xs
concat' xs E = pure xs
concat' xs ys = do
  ys <- value ys
  link xs ys

-- | Assign credits to the thunk and force it
-- unless it is a `LinkAll(t:_)` where `t` requires credits.
-- In the latter case, recursive until we can force a thunk.
dischargeThunk :: MonadInherit m => Thunk m (CLazyCon m) (CatDeque a m) -> m ()
dischargeThunk s = do
  lazymatch s (\_ -> assign) $ \case
    LinkAll q -> do
      q' <- Q.lazyqueue q
      case q' of
        [] -> assign
        t' : _ -> go t'
    Force t -> dischargeThunk t
  where
    assign = creditWith s (costSnoc + costUncons) >> force s >> pure ()
    go t' = lazymatch t' (\_ -> assign) $ \case
      LinkAll _ -> dischargeThunk t'
      Force t -> go t

instance Deque CatDeque where
  empty = pure E
  cons x q = do
    e <- Q.empty
    concat (C x e) q
  snoc q x = do
    e <- Q.empty
    concat q (C x e)
  uncons E = pure Nothing
  uncons (C x q) = do
    q' <- if Q.isEmpty q then pure E else linkTop q
    pure $ Just (x, q')
  unsnoc q = pure $ Just (q, undefined)
  concat = concat'

instance BoundedDeque CatDeque where
  qcost _ (Cons _) = costSnoc
  qcost _ (Snoc _) = costSnoc
  qcost _ Uncons = 4 * costUncons + 3 * costSnoc
  qcost _ Unsnoc = 0
  qcost _ Concat = costSnoc

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (CLazyCon m a) where
  prettyCell (LinkAll q) = do
    q' <- prettyCell q
    pure $ mkMCell "LinkAll" [q']
  prettyCell (Force t) = prettyCell t

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (CatDeque a m) where
  prettyCell E = pure $ mkMCell "E" []
  prettyCell (C x q) = do
    x' <- prettyCell x
    q' <- prettyCell q
    pure $ mkMCell "C" [x', q']

instance Pretty a => MemoryStructure (CatDeque (PrettyCell a)) where
  prettyStructure = prettyCell