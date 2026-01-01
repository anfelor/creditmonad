{-# LANGUAGE GADTs, LambdaCase, QuantifiedConstraints #-}

module Test.Credit.Finger.Simplified where

import Prelude hiding (head, tail, last, init)
import Control.Monad (when, unless)
import Data.Foldable (foldlM, foldrM)
import Prettyprinter (Pretty)

import Control.Monad.Credit
import Test.Credit (linear, log2)
import Test.Credit.Finger.Base (Measured(..), Split(..))
import qualified Test.Credit.Finger.Base as F

data Digit a = One a | Two a a | Three a a a
  deriving (Eq, Ord, Show)

data Tuple v a = Pair v a a | Triple v a a a
  deriving (Eq, Ord, Show)

data Simplified v a m
  = Empty
  | Single a
  | Deep v (Digit a) (Thunk m (FLazyCon m) (Simplified v (Tuple v a) m)) (Digit a)

data FLazyCon m a where
  FCons :: Measured a v => a -> Thunk m (FLazyCon m) (Simplified v a m) -> FLazyCon m (Simplified v a m)
  FSnoc :: Measured a v => Thunk m (FLazyCon m) (Simplified v a m) -> a -> FLazyCon m (Simplified v a m)
  FTail :: Measured a v => Simplified v a m -> FLazyCon m (Simplified v a m)
  FInit :: Measured a v => Simplified v a m -> FLazyCon m (Simplified v a m)

instance MonadCredit m => HasStep (FLazyCon m) m where
  step (FCons x m) = cons x =<< force m
  step (FSnoc m x) = flip snoc x =<< force m
  step (FTail q) = tail q
  step (FInit q) = init q

-- Main idea:
--  - cons, snoc, tail and init all cost two credits
--  - the first credit is used to tick
--  - We maintain the invariant: In each queue Deep(f, m, r), m has ||f| - 2| + ||r| - 2| credits.
--  - The m thunk requires two credits to force.
--  - snoc and tail spend their second credit on either the old m to be able to force it,
--    or on the new m to maintain the invariant.

instance (Eq v, Monoid v) => Measured (Tuple v a) v where
  measure (Pair v _ _) = v
  measure (Triple v _ _ _) = v

instance Measured a v => Measured (Digit a) v where
  measure = measure . toList

instance Measured a v => Measured (Simplified v a m) v where
  measure Empty = mempty
  measure (Single x) = measure x
  measure (Deep vm f m r) = measure f <> vm <> measure r

instance F.FingerTree Simplified where
  empty = Empty
  isEmpty Empty = True
  isEmpty _ = False

  cons = cons
  head = head
  tail = tail

  snoc = snoc
  last = last
  init = init

  concat q1 q2 = glue q1 [] q2
  splitTree = splitTree
  treeToList q = treeToListAcc [] (\x -> [x]) q

instance F.BoundedFingerTree Simplified where
  fcost _ F.Cons = 2
  fcost _ F.Head = 0
  fcost _ F.Tail = 2
  fcost _ F.Snoc = 2
  fcost _ F.Last = 0
  fcost _ F.Init = 2
  fcost n F.Concat = 5 * log2 n
  fcost n F.SplitTree = 5 * log2 n
  fcost n F.TreeToList = 2 * log2 n + 3 * linear n

isTwo :: Digit a -> Bool
isTwo (Two _ _) = True
isTwo _ = False

vempty :: MonadCredit m => m (Thunk m (FLazyCon m) (Simplified v a m))
vempty = value $ Empty

pair :: Measured a v => a -> a -> Tuple v a
pair x y = Pair (measure x <> measure y) x y

triple :: Measured a v => a -> a -> a -> Tuple v a
triple x y z = Triple (measure x <> measure y <> measure z) x y z

deep :: (MonadCredit m, Measured a v) => v -> Digit a -> Thunk m (FLazyCon m) (Simplified v (Tuple v a) m) -> Digit a -> m (Simplified v a m)
deep v f m r = do
  let dang d = if isTwo d then 0 else 1
  m `hasAtLeast` (dang f + dang r)
  lazymatch m (\m -> when (v /= measure m) $ error "invalid measure") (\_ -> pure ())
  pure $ Deep v f m r

deep' :: (MonadCredit m, Measured a v) => v -> Digit a -> m (Thunk m (FLazyCon m) (Simplified v (Tuple v a) m)) -> Digit a -> m (Simplified v a m)
deep' vm f mkM r = do
  m <- mkM
  deep vm f m r

toList :: Digit a -> [a]
toList (One x) = [x]
toList (Two x y) = [x, y]
toList (Three x y z) = [x, y, z]

toTree :: (MonadCredit m, Measured a v) => [a] -> m (Simplified v a m)
toTree [] = pure Empty
toTree [x] = pure $ Single x
toTree [x,y] = deep' mempty (One x) vempty (One y)
toTree [x,y,z] = deep' mempty (Two x y) vempty (One z)

toDigit :: Tuple v a -> Digit a
toDigit (Pair _ x y) = Two x y
toDigit (Triple _ x y z) = Three x y z

cons :: (MonadCredit m, Measured a v) => a -> Simplified v a m -> m (Simplified v a m)
cons x q = do
  tick
  case q of
    Empty -> pure $ Single x
    Single y -> do
      deep' mempty (One x) vempty (One y)
    Deep vq (One y) q u -> do
      deep vq (Two x y) q u
    Deep vq (Two y z) q u -> do
      q `creditWith` 1
      deep vq (Three x y z) q u
    Deep vq (Three y z w) q u -> do
      q' <- delay $ FCons (pair z w) q
      if isTwo u
        then q  `creditWith` 1
        else q' `creditWith` 1
      deep (measure (z, w) <> vq) (Two x y) q' u

head :: MonadCredit m => Simplified v a m -> m a
head Empty = fail "head: empty queue"
head (Single x) = pure x
head (Deep _ s _ _) = pure $ let (h:_) = toList s in h

tail :: (MonadCredit m, Measured a v)
     => Simplified v a m -> m (Simplified v a m)
tail q = do
  tick
  case q of
    Empty -> pure Empty
    Single _ -> pure Empty
    Deep vq (Three _ x y) q u -> do
      deep vq (Two x y) q u
    Deep vq (Two _ x) q u -> do
      q `creditWith` 1
      deep vq (One x) q u
    Deep _ (One _) q u -> do
      when (isTwo u) $ q `creditWith` 1
      force q >>= (`deep0` u)

deep0 :: (MonadCredit m, Measured a v)
      => Simplified v (Tuple v a) m -> Digit a
      -> m (Simplified v a m)
deep0 Empty u = toTree $ toList u
deep0 q u = do
  hd <- head q
  case hd of
    Pair _ x y -> do
      t <- delay $ FTail q
      unless (isTwo u) $ t `creditWith` 1
      let v = measureTail q
      deep v (Two x y) t u
    Triple _ x _ _ -> do
      let q' = map1 chop q
      q'' <- value q'
      deep (measure q') (One x) q'' u
  where chop (Triple _ _ y z) = pair y z

map1 :: (Measured a v) => (a -> a)
     -> Simplified v a m -> Simplified v a m
map1 f q = case q of
  Empty -> Empty
  Single x -> Single (f x)
  Deep v (One x)       m sf -> Deep v (One (f x))       m sf
  Deep v (Two x y)     m sf -> Deep v (Two (f x) y)     m sf
  Deep v (Three x y z) m sf -> Deep v (Three (f x) y z) m sf

measureTail :: Measured a v
            => Simplified v (Tuple v a) m -> v
measureTail q = case q of
  Empty -> mempty
  Single _ -> mempty
  Deep v pr _ sf -> case pr of
    One _       ->                   v <> measure sf
    Two _ y     -> measure y      <> v <> measure sf
    Three _ y z -> measure (y, z) <> v <> measure sf

deepL :: (MonadCredit m, Measured a v) => [a] -> v -> Thunk m (FLazyCon m) (Simplified v (Tuple v a) m) -> Digit a -> m (Simplified v a m)
deepL [] _ m sf = do
  m' <- F.uncons =<< force m
  case m' of
    Nothing -> toTree $ toList sf
    Just (Pair _ x y, m'') -> do
      deep' (measure m'') (Two x y) (value m'') sf
    Just (Triple _ x y z, m'') -> do
      deep' (measure m'') (Three x y z) (value m'') sf
deepL [x] vm m sf = deep vm (One x) m sf
deepL [x,y] vm m sf = deep vm (Two x y) m sf
deepL [x,y,z] vm m sf = deep vm (Three x y z) m sf

last :: (MonadCredit m, Measured a v) => Simplified v a m -> m a
last Empty = fail "last: empty queue"
last (Single x) = pure x
last (Deep _ _ _ s) = pure $ let (h:_) = reverse $ toList s in h

snoc :: (MonadCredit m, Measured a v)
     => Simplified v a m -> a -> m (Simplified v a m)
snoc q w = do
  tick
  case q of
    Empty -> pure $ Single w
    Single x -> do
      deep' mempty (One x) vempty (One w)
    Deep v front middle (One x) ->
      deep v front middle (Two x w)
    Deep v front middle (Two x y) -> do
      middle `creditWith` 1
      deep v front middle (Three x y w)
    Deep v front middle (Three x y z) -> do
      t <- delay $ FSnoc middle (pair x y)
      if isTwo front
        then middle `creditWith` 1
        else t      `creditWith` 1
      deep (v <> measure (x, y)) front t (Two z w)

init :: (MonadCredit m, Measured a v) => Simplified v a m -> m (Simplified v a m)
init q = do
  tick
  case q of
    Empty -> pure Empty
    Single _ -> pure Empty
    Deep vq f q (Three x y _) -> do
      deep vq f q (Two x y)
    Deep vq f q (Two x _) -> do
      q `creditWith` 1
      deep vq f q (One x)
    Deep _ f q (One _) -> do
      when (isTwo f) $
        q `creditWith` 1
      deepN f =<< force q

deepN :: (MonadCredit m, Measured a v) => Digit a -> Simplified v (Tuple v a) m -> m (Simplified v a m)
deepN s Empty = toTree $ toList s
deepN s (Single (Pair _ x y)) = do
  deep' mempty s vempty (Two x y)
deepN s (Single (Triple _ x y z)) = do
  deep' (measure x <> measure y) s (value (Single (pair x y))) (One z)
deepN u (Deep vq pr q sf) = do
  case chopN sf of
    Left (vsf', x, y) -> do
      t <- delay $ FInit (Deep vq pr q sf)
      unless (isTwo u) $ creditWith t 1
      deep (measure pr <> vq <> vsf') u t (Two x y)
    Right (sf', x) -> do
      deep' (measure pr <> vq <> measure sf') u (value (Deep vq pr q sf')) (One x)

chopN :: (Measured a v) => Digit (Tuple v a) -> Either (v, a, a) (Digit (Tuple v a), a)
chopN (One (Pair _ x y)) = Left (mempty, x, y)
chopN (Two x (Pair _ y z)) = Left (measure x, y, z)
chopN (Three x y (Pair _ z w)) = Left (measure x <> measure y, z, w)
chopN (One (Triple _ x y z)) = Right (One (pair x y), z)
chopN (Two x (Triple _ y z w)) = Right (Two x (pair y z), w)
chopN (Three x y (Triple _ z w u)) = Right (Three x y (pair z w), u)

deepR :: (MonadCredit m, Measured a v) => Digit a -> v -> Thunk m (FLazyCon m) (Simplified v (Tuple v a) m) -> [a] -> m (Simplified v a m)
deepR s _ m [] = do
  m' <- F.unsnoc =<< force m
  case m' of
    Nothing -> toTree $ toList s
    Just (m'', Pair _ x y) -> do
      deep' (measure m'') s (value m'') (Two x y)
    Just (m'', Triple _ x y z) -> do
      deep' (measure m'') s (value m'') (Three x y z)
deepR s vm m [x] = deep vm s m (One x)
deepR s vm m [x, y] = deep vm s m (Two x y)
deepR s vm m [x, y, z] = deep vm s m (Three x y z)

toTuples :: Measured a v => [a] -> [Tuple v a]
toTuples [] = []
toTuples [x, y] = [pair x y]
toTuples [x, y, z, w] = [pair x y, pair z w]
toTuples (x : y : z : xs) = triple x y z : toTuples xs

glue :: (MonadCredit m, Measured a v) => Simplified v a m -> [a] -> Simplified v a m -> m (Simplified v a m)
glue Empty as q2 = foldrM cons q2 as
glue q1 as Empty = foldlM snoc q1 as
glue (Single x) as q2 = foldrM cons q2 (x : as)
glue q1 as (Single y) = foldlM snoc q1 (as ++ [y])
glue (Deep _ u1 q1 v1) as (Deep _ u2 q2 v2) = tick >> do
  creditWith q1 2
  q1 <- force q1
  creditWith q2 2
  q2 <- force q2
  q <- glue q1 (toTuples (toList v1 ++ as ++ toList u2)) q2
  deep' (measure q) u1 (value q) v2

splitDigit :: Measured a v => (v -> Bool) -> v -> Digit a -> ([a], a, [a])
splitDigit p i (One x) = ([], x, [])
splitDigit p i (Two x y)
  | p (i <> measure x) = ([], x, [y])
  | otherwise = ([x], y, [])
splitDigit p i (Three x y z)
  | p (i <> measure x) = ([], x, [y, z])
  | p (i <> measure x <> measure y) = ([x], y, [z])
  | otherwise = ([x, y], z, [])

splitTree :: (MonadCredit m, Measured a v) => (v -> Bool) -> v -> Simplified v a m -> m (Split Simplified v a m)
splitTree p i Empty = fail "splitTree: empty tree"
splitTree p i (Single x) = pure $ Split Empty x Empty
splitTree p i (Deep vm pr m sf) = do
  tick
  m `creditWith` 2
  let vpr = i <> measure pr
  let vprm = vpr <> vm
  if p vpr then do
    let (l, x, r) = splitDigit p i pr
    Split <$> toTree l <*> pure x <*> deepL r vm m sf
  else if p vprm then do
    Split ml xs mr <- splitTree p vpr =<< force m
    let vml = measure ml
    let (l, x, r) = splitDigit p (vpr <> vml) (toDigit xs)
    [ml', mr'] <- mapM value [ml, mr]
    Split <$> deepR pr vml ml' l <*> pure x <*> deepL r (measure mr) mr' sf
  else do
    let (l, x, r) = splitDigit p vprm sf
    Split <$> deepR pr vm m l <*> pure x <*> toTree r

rev :: MonadCredit m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc) 

append :: MonadCredit m => [a] -> [a] -> m [a]
append [] ys = pure ys
append (x : xs) ys = tick >> fmap (x:) (append xs ys)

treeToListAcc :: MonadCredit m => [b] -> (a -> [b]) -> Simplified v a m -> m [b]
treeToListAcc acc f Empty = rev acc []
treeToListAcc acc f (Single x) = do
  flip rev [] =<< append (f x) acc
treeToListAcc acc f (Deep _ s q u) = do
  let s' = concatMap f $ toList s
  let u' = concatMap f $ toList u
  creditWith q 2
  q' <- treeToListAcc (u' ++ acc) (concatMap f . toList . toDigit) =<< force q
  append s' q'

instance MemoryCell m a => MemoryCell m (Digit a) where
  prettyCell (One a) = do
    a' <- prettyCell a
    pure $ mkMCell "One" [a']
  prettyCell (Two a b) = do
    a' <- prettyCell a
    b' <- prettyCell b
    pure $ mkMCell "Two" [a', b']
  prettyCell (Three a b c) = do
    a' <- prettyCell a
    b' <- prettyCell b
    c' <- prettyCell c
    pure $ mkMCell "Three" [a', b', c']

instance MemoryCell m a => MemoryCell m (Tuple v a) where
  prettyCell (Pair _ a b) = do
    a' <- prettyCell a
    b' <- prettyCell b
    pure $ mkMCell "Pair" [a', b']
  prettyCell (Triple _ a b c) = do
    a' <- prettyCell a
    b' <- prettyCell b
    c' <- prettyCell c
    pure $ mkMCell "Triple" [a', b', c']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (FLazyCon m a) where
  prettyCell (FCons x m) = do
    -- x' <- prettyCell x
    m' <- prettyCell m
    pure $ mkMCell "FCons" [m']
  prettyCell (FSnoc m x) = do
    m' <- prettyCell m
    -- x' <- prettyCell x
    pure $ mkMCell "FSnoc" [m']
  prettyCell (FTail q) = do
    q' <- prettyCell q
    pure $ mkMCell "FTail" [q']
  prettyCell (FInit q) = do
    q' <- prettyCell q
    pure $ mkMCell "FInit" [q']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Simplified v a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Single a) = do
    a' <- prettyCell a
    pure $ mkMCell "Single" [a']
  prettyCell (Deep _ s q u) = do
    s' <- prettyCell s
    q' <- prettyCell q
    u' <- prettyCell u
    pure $ mkMCell "Deep" [s', q', u']

instance (forall m. Monad m => MemoryCell m a) => MemoryStructure (Simplified v a) where
  prettyStructure = prettyCell