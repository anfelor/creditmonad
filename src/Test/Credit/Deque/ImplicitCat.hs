module Test.Credit.Deque.ImplicitCat where

import Prelude hiding (head, tail, concat)
import Control.Monad (join, when)
import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Deque.Base
import qualified Test.Credit.Deque.Base as D
import qualified Test.Credit.Deque.Bankers as D

data ImplicitCat a m
  = Shallow (D.BDeque a m)
  | Deep (D.BDeque a m) -- ^ (>= 3 elements)
         (Thunk m (ILazyCon m) (ImplicitCat (CmpdElem a m) m))
         (D.BDeque a m) -- ^ (>= 2 elements)
         (Thunk m (ILazyCon m) (ImplicitCat (CmpdElem a m) m))
         (D.BDeque a m) -- ^ (>= 3 elements)

data ILazyCon m a where
  IPay :: (Thunk m (ILazyCon m) (ImplicitCat (CmpdElem a m) m)) -> m b -> ILazyCon m b
  ILazy :: m a -> ILazyCon m a

instance MonadCredit m => HasStep (ILazyCon m) m where
  step (IPay _ m) = m
  step (ILazy m) = m

data CmpdElem a m
  = Simple (D.BDeque a m)
  | Cmpd (D.BDeque a m) -- ^ (>= 2 elements)
         (Thunk m (ILazyCon m) (ImplicitCat (CmpdElem a m) m))
         (D.BDeque a m) -- ^ (>= 2 elements)

-- The O(1) unshared cost of operations
-- Each thunk in the program requires at most 5 * cost credits to run
-- except for the thunks returned by uncons/unsnoc which require
-- 6 * cost credits to run.
cost :: Credit
cost = 3 * (qcost @(D.BDeque) undefined (Cons undefined) + qcost @(D.BDeque) undefined Uncons)

deepDanger :: D.BDeque a m -> Credit
deepDanger d = if D.size d == 3 then cost else 0

deep :: MonadCredit m
     => D.BDeque a m
     -> Thunk m (ILazyCon m) (ImplicitCat (CmpdElem a m) m)
     -> D.BDeque a m
     -> Thunk m (ILazyCon m) (ImplicitCat (CmpdElem a m) m)
     -> D.BDeque a m
     -> m (ImplicitCat a m)
deep f a m b r = do
  -- a `hasAtLeast` (4 * deepDanger f + deepDanger r)
  -- b `hasAtLeast` (deepDanger f + 4 * deepDanger r)
  pure $ Deep f a m b r

icreditWith :: MonadCredit m => Thunk m (ILazyCon m) (ImplicitCat a m) -> Credit -> m ()
icreditWith t c = do
  lazymatch t (\_ -> pure ()) $ \t'' -> case t'' of
    ILazy _ ->   t  `creditWith` c
    IPay t' _ -> t' `creditWith` c

cmpdDanger :: D.BDeque a m -> Credit
cmpdDanger d = if D.size d == 2 then cost else 0

cmpd :: MonadCredit m
     => D.BDeque a m
     -> Thunk m (ILazyCon m) (ImplicitCat (CmpdElem a m) m)
     -> D.BDeque a m
     -> m (CmpdElem a m)
cmpd f c r = pure $ Cmpd f c r

isEmpty :: ImplicitCat a m -> Bool
isEmpty (Shallow d) = D.isEmpty d
isEmpty (Deep _ _ _ _ _) = False

share :: MonadInherit m => D.BDeque a m -> D.BDeque a m -> m (D.BDeque a m, D.BDeque a m, D.BDeque a m)
share f r = do
  fu <- D.unsnoc f
  ru <- D.uncons r
  case (fu, ru) of
    (Just (fi, fl), Just (rh, rt)) -> do
      m <- D.cons fl =<< D.cons rh =<< D.empty
      pure $ (fi, m, rt)
    _ -> fail "share: empty deque"

dappendL :: MonadInherit m => D.BDeque a m -> D.BDeque a m -> m (D.BDeque a m)
dappendL d1 d2 = do
  d1' <- D.unsnoc d1
  case d1' of
    Nothing -> pure d2
    Just (d1i, d1l) -> dappendL d1i =<< D.cons d1l d2

dappendR :: MonadInherit m => D.BDeque a m -> D.BDeque a m -> m (D.BDeque a m)
dappendR d1 d2 = do
  d2' <- D.uncons d2
  case d2' of
    Nothing -> pure d1
    Just (d2h, d2t) -> join $ dappendR <$> D.snoc d1 d2h <*> pure d2t

-- 5 * cost
concat' :: MonadInherit m => ImplicitCat a m -> ImplicitCat a m -> m (ImplicitCat a m)
concat' (Shallow d1) (Shallow d2) = do
  if D.size d1 < 4 then Shallow <$> dappendL d1 d2
  else if D.size d2 < 4 then Shallow <$> dappendR d1 d2
  else do
    (f, m, r) <- share d1 d2
    e <- delay $ ILazy $ empty
    deep f e m e r
concat' (Shallow d) (Deep f a m b r) = do
  if D.size d < 4 then do
    df <- dappendL d f
    deep df a m b r
  else do
    fa <- delay $ ILazy $ do
      a `icreditWith` (5 * cost)
      cons (Simple f) =<< force a
    fa `icreditWith` cost
    fa `icreditWith` (deepDanger r)
    deep d fa m b r
concat' (Deep f a m b r) (Shallow d) = do
  if D.size d < 4 then do
    rd <- dappendR r d
    deep f a m b rd
  else do
    br <- delay $ ILazy $ do
      b `icreditWith` (5 * cost)
      (`snoc` (Simple r)) =<< force b
    br `icreditWith` cost
    br `icreditWith` (deepDanger f)
    deep f a m br d
concat' (Deep f1 a1 m1 b1 r1) (Deep f2 a2 m2 b2 r2) = do
  (r1', m, f2') <- share r1 f2
  -- Discharge debits on b1, a2 for compound element
  when (D.size f1 > 3 && D.size r1 > 3) $
    b1 `icreditWith` cost
  when (D.size f2 > 3 && D.size r2 > 3) $
    a2 `icreditWith` cost
  c1 <- cmpd m1 b1 r1'
  c2 <- cmpd f2' a2 m2
  a1' <- delay $ ILazy $ do
    a1 `icreditWith` (4 * (cost - deepDanger f1))
    (`snoc` c1) =<< force a1
  b2' <- delay $ ILazy $ do
    b2 `icreditWith` (4 * (cost - deepDanger r2))
    cons c2 =<< force b2
  -- Discharge debits for snoc/cons onto a1/b2
  a1' `icreditWith` cost
  b2' `icreditWith` cost
  -- Discharge the debit from swapping f/r
  when (D.size f1 == 3 && D.size f2 > 3) $
    b2 `icreditWith` cost
  when (D.size r2 == 3 && D.size r1 > 3) $
    a1 `icreditWith` cost
  -- Notice that only two of the when-statements
  -- can be true at the same time.
  -- So we only discharge 4 debits.
  deep f1 a1' m b2' r2

replaceHead :: MonadInherit m => a -> ImplicitCat a m -> m (ImplicitCat a m)
replaceHead x (Shallow d) = do
  d' <- D.uncons d
  case d' of
    Nothing -> fail "replaceHead: empty deque"
    Just (_, d') -> Shallow <$> D.cons x d'
replaceHead x (Deep f a m b r) = do
  f' <- D.uncons f
  case f' of
    Nothing -> fail "replaceHead: empty deque"
    Just (_, f') -> do
      f' <- D.cons x f'
      deep f' a m b r

-- 6 * cost + 1 tick
-- TODO: is there an off-by-one error here?
-- We assign 5 * cost to other thunks and also perform 1 * cost of work.
-- So the cost of the thunk is 6 * cost, not 5 * cost as claimed by Okasaki.
-- In particular consider the case where a = empty and uncons b returns a compound element.
-- Here we need to assign an extra 1 * cost to the bt thunk, but we can't possibly pay for that.
-- Does that mean that this function is not amortized O(1)?
-- This doesn't show up in the testsuite, because we never concat two deep deques
-- and so we never generate a deque with a compound element.
uncons' :: MonadInherit m => ImplicitCat a m -> m (Maybe (a, Thunk m (ILazyCon m) (ImplicitCat a m)))
uncons' (Shallow d) = tick >> do
  m <- D.uncons d
  case m of
    Nothing -> pure Nothing
    Just (x, d') -> fmap (Just . (x,)) $ delay $ ILazy $ do
      pure $ Shallow d'
uncons' (Deep f a m b r) = tick >> do
  f' <- D.uncons f
  case f' of
    Nothing -> pure Nothing
    Just (x, f') -> fmap (Just . (x,)) $ delay $ ILazy $ do
      if D.size f' >= 3 -- iff D.size f > 3
        then do
          a `icreditWith` (4 * deepDanger f')
          b `icreditWith` (deepDanger f')
          deep f' a m b r
        else do -- D.size f' == 2
          a `icreditWith` (cost - deepDanger r)
          a <- force a
          if not (isEmpty a)
            then do
              a' <- uncons' a
              case a' of
                Nothing -> fail "uncons': a cannot be empty"
                Just (ah, at) -> do
                  case ah of
                    Simple d -> do
                      f'' <- dappendL f' d -- cost: 2 * (cons + unsnoc)
                      at `icreditWith` cost
                      at `icreditWith` (deepDanger r)
                      deep f'' at m b r
                    Cmpd f'' c' r' -> do
                      f''' <- dappendL f' f'' -- cost: 2 * (cons + unsnoc)
                      a'' <- delay $ ILazy $ do
                        c'' <- force c'
                        ra <- replaceHead (Simple r') a -- cost: uncons + cons
                        concat' c'' ra
                      c' `icreditWith` (4 * cost)
                      a'' `icreditWith` (deepDanger r)
                      deep f''' a'' m b r
            else do
              b `icreditWith` (4 * (cost - deepDanger r))
              b <- force b
              if not (isEmpty b)
                then do
                  b' <- uncons' b
                  case b' of
                    Nothing -> fail "uncons': b cannot be empty"
                    Just (bh, bt) -> do
                      case bh of
                        Simple d -> do
                          f'' <- dappendL f' m -- cost: 2 * (cons + unsnoc)
                          -- TODO: this is ugly. Since bt has 6 * cost debits
                          -- we need to assign 1 * cost extra credits to it. But we
                          -- can not pay for that. Instead, we redirect credits
                          -- passed to a to be sent to bt. Once r is in deepDanger,
                          -- it will pass one credit to a, which is redirected to bt.
                          -- This ensures that bt receives 6 * cost credits by the
                          -- time it is forced.
                          a <- delay $ IPay bt $ do
                            fmap Shallow $ empty
                          a `icreditWith` (deepDanger r)
                          bt `icreditWith` (4 * deepDanger r)
                          deep f'' a d bt r
                        Cmpd f'' c' r' -> do
                          f''' <- dappendL f' m -- cost: 2 * (cons + unsnoc)
                          a'' <- delay $ ILazy $ do
                            c' `icreditWith` (4 * cost)
                            cons (Simple f'') =<< force c'
                          a'' `icreditWith` (deepDanger r)
                          bt `icreditWith` (4 * deepDanger r)
                          -- TODO: Here bt has too many debits: it gets 6 * cost
                          -- debits from uncons', but may only have 5 * cost.
                          -- We have already exhausted the credits on the current
                          -- thunk and cannot pay for the extra 1 * cost.
                          deep f''' a'' r' bt r
                else do -- 1 * cost
                  fm <- dappendL f' m
                  concat' (Shallow fm) (Shallow r)

replaceLast :: MonadInherit m => ImplicitCat a m -> a -> m (ImplicitCat a m)
replaceLast (Shallow d) x = do
  d' <- D.unsnoc d
  case d' of
    Nothing -> fail "replaceLast: empty deque"
    Just (d', _) -> Shallow <$> D.snoc d' x
replaceLast (Deep f a m b r) x = do
  r' <- D.unsnoc r
  case r' of
    Nothing -> fail "replaceLast: empty deque"
    Just (r', _) -> do
      r' <- D.snoc r' x
      deep f a m b r'

unsnoc' :: MonadInherit m => ImplicitCat a m -> m (Maybe (Thunk m (ILazyCon m) (ImplicitCat a m), a))
unsnoc' (Shallow d) = tick >> do
  m <- D.unsnoc d
  case m of
    Nothing -> pure Nothing
    Just (d', x) -> fmap (Just . (,x)) $ delay $ ILazy $ do
      pure $ Shallow d'
unsnoc' (Deep f a m b r) = tick >> do
  r' <- D.unsnoc r
  case r' of
    Nothing -> pure Nothing
    Just (r', x) -> fmap (Just . (,x)) $ delay $ ILazy $ do
      if D.size r' >= 3 -- iff D.size r > 3
        then do
          a `icreditWith` (deepDanger r')
          b `icreditWith` (4 * deepDanger r')
          deep f a m b r'
        else do
          b `icreditWith` (cost - deepDanger f)
          b <- force b
          if not (isEmpty b)
            then do
              b' <- unsnoc' b
              case b' of
                Nothing -> fail "unsnoc': b cannot be empty"
                Just (bi, bl) -> do
                  case bl of
                    Simple d -> do
                      r'' <- dappendR d r'
                      bi `icreditWith` cost
                      bi `icreditWith` (deepDanger f)
                      deep f a m bi r''
                    Cmpd f' c' r'' -> do
                      r''' <- dappendR r'' r'
                      b'' <- delay $ ILazy $ do
                        c'' <- force c'
                        bf <- replaceLast b (Simple f')
                        concat' bf c''
                      c' `icreditWith` (4 * cost)
                      b'' `icreditWith` (deepDanger f)
                      deep f a m b'' r'''
            else do
              a `icreditWith` (4 * (cost - deepDanger f))
              a <- force a
              if not (isEmpty a)
                then do
                  a' <- unsnoc' a
                  case a' of
                    Nothing -> fail "unsnoc': a cannot be empty"
                    Just (ai, al) -> do
                      case al of
                        Simple d -> do
                          r'' <- dappendR m r'
                          b <- delay $ IPay ai $ do
                            fmap Shallow $ empty
                          b `icreditWith` (deepDanger f)
                          ai `icreditWith` (4 * deepDanger f)
                          deep f ai d b r''
                        Cmpd f' c' r'' -> do
                          r''' <- dappendR m r'
                          b'' <- delay $ ILazy $ do
                            c' `icreditWith` (4 * cost)
                            (`snoc` (Simple r'')) =<< force c'
                          b'' `icreditWith` (deepDanger f)
                          ai `icreditWith` (4 * deepDanger f)
                          deep f ai f' b'' r'''
                else do
                  mr <- dappendR m r'
                  concat' (Shallow f) (Shallow mr)

instance Deque ImplicitCat where
  empty = Shallow <$> D.empty
  cons x (Shallow d) = Shallow <$> D.cons x d
  cons x (Deep f a m b r) = do
    f' <- D.cons x f
    deep f' a m b r
  snoc (Shallow d) x = Shallow <$> D.snoc d x
  snoc (Deep f a m b r) x = Deep f a m b <$> D.snoc r x
  uncons d = do
    m <- uncons' d
    case m of
      Nothing -> pure Nothing
      Just (x, t) -> do
        t `icreditWith` (6 * cost)
        Just . (x,) <$> force t
  unsnoc d = do
    m <- unsnoc' d
    case m of
      Nothing -> pure Nothing
      Just (t, x) -> do
        t `icreditWith` (6 * cost)
        Just . (,x) <$> force t
  concat xs ys = tick >> concat' xs ys

instance BoundedDeque ImplicitCat where
  qcost sz (Cons x) = qcost @(D.BDeque) sz (Cons x)
  qcost sz (Snoc x) = qcost @(D.BDeque) sz (Snoc x)
  qcost sz Uncons = 1 + 6 * cost + qcost @(D.BDeque) sz Uncons
  qcost sz Unsnoc = 1 + 6 * cost + qcost @(D.BDeque) sz Unsnoc
  qcost _ Concat = 1 + 5 * cost

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (ILazyCon m a) where
  prettyCell _ = pure $ mkMCell "<lazy>" []

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (CmpdElem a m) where
  prettyCell (Simple d) = do
    d' <- prettyCell d
    pure $ mkMCell "Simple" [d']
  prettyCell (Cmpd f m r) = do
    f' <- prettyCell f
    m' <- prettyCell m
    r' <- prettyCell r
    pure $ mkMCell "Cmpd" [f', m', r']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (ImplicitCat a m) where
  prettyCell (Shallow d) = do
    d' <- prettyCell d
    pure $ mkMCell "Shallow" [d']
  prettyCell (Deep f a m b r) = do
    f' <- prettyCell f
    a' <- prettyCell a
    m' <- prettyCell m
    b' <- prettyCell b
    r' <- prettyCell r
    pure $ mkMCell "Deep" [f', a', m', b', r']

instance Pretty a => MemoryStructure (ImplicitCat (PrettyCell a)) where
  prettyStructure = prettyCell