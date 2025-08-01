{-# LANGUAGE TypeFamilies #-}

module Test.Credit.Heap.Scheduled where

import Prettyprinter (Pretty)
import Control.Monad.Credit
import Test.Credit
import Test.Credit.Heap.Base

data Stream m a
  = SCons a (Stream m a)
  | SNil
  | SIndirect (Thunk m (Lazy m) (Stream m a))

indirect :: MonadCredit m => m (Stream m a) -> m (Stream m a)
indirect = fmap SIndirect . delay . Lazy

credit :: MonadCredit m => Credit -> Stream m a -> m ()
credit cr (SIndirect i) = creditWith i cr
credit _ _ = pure ()

-- | Smart destructor for streams, consuming one credit
smatch :: MonadCredit m => Stream m a -- ^ Scrutinee
       -> m b -- ^ Nil case
       -> (a -> Stream m a -> m b) -- ^ Cons case
       -> m b
smatch x nil cons = tick >> eval x
  where
    eval x = case x of
      SCons a as -> cons a as
      SNil -> nil
      SIndirect i -> force i >>= eval

data Tree a = Node a [Tree a]
  deriving (Eq, Ord, Show)

data Digit a = Zero | One (Tree a)
  deriving (Eq, Ord, Show)

type Schedule m a = [Stream m (Digit a)]

data Scheduled a m = Scheduled (Stream m (Digit a)) (Schedule m a)

link :: Ord a => Tree a -> Tree a -> Tree a
link t1@(Node x1 c1) t2@(Node x2 c2)
  | x1 <= x2 = Node x1 (t2:c1)
  | otherwise = Node x2 (t1:c2)

insTree :: MonadCredit m => Ord a => Tree a -> Stream m (Digit a) -> m (Stream m (Digit a))
insTree t s = smatch s
  (pure $ SCons (One t) SNil)
  (\d ds -> case d of
    Zero -> pure $ SCons (One t) ds
    One t' -> indirect $ do
      SCons Zero <$> insTree (link t t') ds)

mrg :: MonadCredit m => Ord a => Stream m (Digit a) -> Stream m (Digit a) -> m (Stream m (Digit a))
mrg ds1 ds2 = credit 1 ds1 >> smatch ds1
  (pure ds2)
  (\d1 ds1 -> credit 1 ds1 >> smatch ds2
    (pure $ SCons d1 ds1)
    (\d2 ds2 -> case (d1, d2) of
      (Zero, _) -> SCons d2 <$> mrg ds1 ds2
      (_, Zero) -> SCons d1 <$> mrg ds1 ds2
      (One t1, One t2) -> SCons Zero <$> (insTree (link t1 t2) =<< mrg ds1 ds2)))

normalize :: MonadCredit m => Ord a => Stream m (Digit a) -> m ()
normalize ds = credit 1 ds >> smatch ds
    (pure ())
    (\_ ds -> normalize ds)

exec :: MonadCredit m => Schedule m a -> m (Schedule m a)
exec [] = pure []
exec (ds:dss) = credit 1 ds >> smatch ds
  (pure dss)
  (\d job -> case d of
    Zero -> pure $ job:dss
    One _ -> pure dss)

removeMinTree :: MonadCredit m => Ord a => Stream m (Digit a) -> m (Tree a, Stream m (Digit a))
removeMinTree ds = credit 1 ds >> smatch ds
  (fail "removeMinTree: empty stream")
  (\d ds -> case d of
      Zero -> do 
        (t', ds') <- removeMinTree ds
        pure (t', SCons Zero ds')
      One (t@(Node x _)) -> credit 1 ds >> smatch ds
        (pure (t, SNil))
        (\_ _ -> do
          (t'@(Node x' _), ds') <- removeMinTree ds
          if x <= x'
            then pure (t, SCons Zero ds)
            else pure (t', SCons (One t) ds')))

revOneStream :: MonadCredit m => [Tree a] -> Stream m (Digit a) -> m (Stream m (Digit a))
revOneStream [] acc = pure acc
revOneStream (t:ts) acc = tick >> revOneStream ts (SCons (One t) acc)

instance Heap Scheduled where
  empty = pure $ Scheduled SNil []
  insert x (Scheduled ds sched) = do
    ds' <- insTree (Node x []) ds -- 1
    sched' <- exec =<< exec (ds':sched) -- 2 + 2
    pure $ Scheduled ds' sched'
  merge (Scheduled ds1 _) (Scheduled ds2 _) = do
    normalize ds1 -- log2 n1
    normalize ds2 -- log2 n2
    ds <- mrg ds1 ds2 -- 5 * log2 (n1 + n2)
    normalize ds -- log2 (n1 + n2)
    pure $ Scheduled ds []
  splitMin (Scheduled ds sched) = smatch ds
    (pure Nothing)
    (\_ _ -> do
      (Node x c, ds') <- removeMinTree ds -- 4 * log2 n
      c' <- revOneStream c SNil -- log2 n
      ds'' <- mrg c' ds' -- 5 * log2 (n1 + n2)
      normalize ds'' -- log2 (n1 + n2)
      pure (Just (x, Scheduled ds'' [])))

instance BoundedHeap Scheduled where
  hcost _ (Insert _) = 5
  hcost n Merge = 8 * (1 + log2 n)
  hcost n SplitMin = 1 + 5 * log2 n + 6 * log2 (2 * n)

instance MemoryCell m a => MemoryCell m (Tree a) where
  prettyCell (Node x c) = do
    x' <- prettyCell x
    c' <- mapM prettyCell c
    pure $ mkMCell "Node" [x', mkMList c' Nothing]

instance MemoryCell m a => MemoryCell m (Digit a) where
  prettyCell Zero = pure $ mkMCell "Zero" []
  prettyCell (One t) = mkMCell "One" . (:[]) <$> prettyCell t

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Stream m a) where
  prettyCell xs = mkMList <$> toList xs <*> toHole xs
    where
      toList SNil = pure $ []
      toList (SCons x xs) = (:) <$> prettyCell x <*> toList xs
      toList (SIndirect t) = pure $ []

      toHole SNil = pure $ Nothing
      toHole (SCons x xs) = toHole xs
      toHole (SIndirect t) = Just <$> prettyCell t

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Scheduled a m) where
  prettyCell (Scheduled ds sched) = do
    ds' <- prettyCell ds
    sched' <- mapM prettyCell sched
    pure $ mkMCell "Scheduled" [ds', mkMList sched' Nothing]

instance Pretty a => MemoryStructure (Scheduled (PrettyCell a)) where
  prettyStructure = prettyCell