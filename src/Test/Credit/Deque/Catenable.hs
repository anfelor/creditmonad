{-# LANGUAGE GADTs, LambdaCase #-}

module Test.Credit.Deque.Catenable where

import Prelude hiding (concat)
import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit.Deque.Base
import qualified Test.Credit.Queue.Base as Q
import qualified Test.Credit.Queue.Bankers as Q

-- | A rose tree where the elements are pre-ordered
data CatDeque a m
  = E
  | C a -- ^ head
      (Q.BQueue (Thunk m (CLazyCon m) (CatDeque a m)) m) -- ^ tail

data CLazyCon m a where
  LinkAll :: Q.BQueue (Thunk m (CLazyCon m) (CatDeque a m)) m -> CLazyCon m (CatDeque a m)

instance MonadInherit m => HasStep (CLazyCon m) m where
  step (LinkAll q) = linkAll q

costSnoc :: Credit
costSnoc = Q.qcost @(Q.BQueue) undefined (Q.Snoc undefined)

costUncons :: Credit
costUncons = Q.qcost @(Q.BQueue) undefined (Q.Uncons)

link :: MonadInherit m => CatDeque a m -> Thunk m (CLazyCon m) (CatDeque a m) -> m (CatDeque a m)
link (C x q) s = C x <$> Q.snoc q s

linkAll :: MonadInherit m => Q.BQueue (Thunk m (CLazyCon m) (CatDeque a m)) m -> m (CatDeque a m)
linkAll q = do
  m <- Q.uncons q
  case m of
    Nothing -> fail "linkAll: empty queue"
    Just (t, q') -> do
      t <- force t
      if Q.isEmpty q' then pure t
      else do
        s <- delay $ LinkAll q'
        creditWith s costUncons -- for the last uncons
        link t s

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
  let assign = creditWith s (costSnoc + costUncons) >> force s >> pure ()
  lazymatch s (\_ -> assign) $ \case
    LinkAll q -> do
      q' <- Q.lazyqueue q
      case q' of
        [] -> assign
        t' : _ -> do
          lazymatch t' (\_ -> assign) $ \case
            LinkAll _ -> dischargeThunk t'

findFirstThunk :: MonadInherit m => CatDeque a m -> m (Maybe (Thunk m (CLazyCon m) (CatDeque a m)))
findFirstThunk (C _ q) = do
  q' <- Q.lazyqueue q
  seekFirstThunk q'
findFirstThunk _ = pure Nothing

seekFirstThunk :: MonadInherit m => [Thunk m (CLazyCon m) (CatDeque a m)] -> m (Maybe (Thunk m (CLazyCon m) (CatDeque a m)))
seekFirstThunk [] = pure Nothing
seekFirstThunk (t : q) = do
  mt <- lazymatch t findFirstThunk $ \case
    LinkAll _ -> pure $ Just t
  case mt of
    Nothing -> seekFirstThunk q
    Just t' -> pure $ Just t'

dischargeFirst :: MonadInherit m => CatDeque a m -> m ()
dischargeFirst q = do
  mt <- findFirstThunk q
  case mt of
    Nothing -> pure ()
    Just t -> dischargeThunk t

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
    q' <- if Q.isEmpty q then pure E else linkAll q
    dischargeFirst q'
    dischargeFirst q'
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

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (CatDeque a m) where
  prettyCell E = pure $ mkMCell "E" []
  prettyCell (C x q) = do
    x' <- prettyCell x
    q' <- prettyCell q
    pure $ mkMCell "C" [x', q']

instance Pretty a => MemoryStructure (CatDeque (PrettyCell a)) where
  prettyStructure = prettyCell