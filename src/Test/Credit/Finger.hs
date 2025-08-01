{-# LANGUAGE GADTs, LambdaCase #-}

module Test.Credit.Finger where

import Prelude hiding (head, tail, last, init)
import Control.Monad (when, unless)
import Data.Foldable (foldlM, foldrM)
import Prettyprinter (Pretty)

import Control.Monad.Credit
import Test.Credit (linear, log2)
import qualified Test.Credit.Deque.Base as D
import qualified Test.Credit.Heap.Base as H
import qualified Test.Credit.RandomAccess.Base as RA
import qualified Test.Credit.Sortable.Base as S

data Digit a = One a | Two a a | Three a a a
  deriving (Eq, Ord, Show)

data Tuple v a = Pair v a a | Triple v a a a
  deriving (Eq, Ord, Show)

data FingerTree v a m
  = Empty
  | Single a
  | Deep v (Digit a) (Thunk m (FLazyCon m) (FingerTree v (Tuple v a) m)) (Digit a)

data FLazyCon m a where
  FCons :: Measured a v => a -> Thunk m (FLazyCon m) (FingerTree v a m) -> FLazyCon m (FingerTree v a m)
  FSnoc :: Measured a v => Thunk m (FLazyCon m) (FingerTree v a m) -> a -> FLazyCon m (FingerTree v a m)
  FTail :: Measured a v => FingerTree v a m -> FLazyCon m (FingerTree v a m)
  FInit :: Measured a v => FingerTree v a m -> FLazyCon m (FingerTree v a m)

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

class (Eq v, Monoid v) => Measured a v where
  measure :: a -> v

instance (Eq v, Monoid v) => Measured (Tuple v a) v where
  measure (Pair v _ _) = v
  measure (Triple v _ _ _) = v

instance Measured a v => Measured (Digit a) v where
  measure = measure . toList

instance Measured a v => Measured [a] v where
  measure = mconcat . map measure

instance Measured a v => Measured (FingerTree v a m) v where
  measure Empty = mempty
  measure (Single x) = measure x
  measure (Deep vm f m r) = measure f <> vm <> measure r

isTwo :: Digit a -> Bool
isTwo (Two _ _) = True
isTwo _ = False

empty :: MonadCredit m => m (Thunk m (FLazyCon m) (FingerTree v a m))
empty = value $ Empty

pair :: Measured a v => a -> a -> Tuple v a
pair x y = Pair (measure x <> measure y) x y

triple :: Measured a v => a -> a -> a -> Tuple v a
triple x y z = Triple (measure x <> measure y <> measure z) x y z

deep :: (MonadCredit m, Measured a v) => v -> Digit a -> Thunk m (FLazyCon m) (FingerTree v (Tuple v a) m) -> Digit a -> m (FingerTree v a m)
deep v f m r = do
  let dang d = if isTwo d then 0 else 1
  mIsPure <- lazymatch m (\_ -> pure True) (\_ -> pure False)
  unless mIsPure $
    m `hasAtLeast` (dang f + dang r)
  lazymatch m (\m -> when (v /= measure m) $ error "invalid measure") (\_ -> pure ())
  pure $ Deep v f m r

deep' :: (MonadCredit m, Measured a v) => v -> Digit a -> m (Thunk m (FLazyCon m) (FingerTree v (Tuple v a) m)) -> Digit a -> m (FingerTree v a m)
deep' vm f mkM r = do
  m <- mkM
  deep vm f m r

isEmpty :: FingerTree v a m -> Bool
isEmpty Empty = True
isEmpty _ = False

toList :: Digit a -> [a]
toList (One x) = [x]
toList (Two x y) = [x, y]
toList (Three x y z) = [x, y, z]

toTree :: (MonadCredit m, Measured a v) => [a] -> m (FingerTree v a m)
toTree [] = pure Empty
toTree [x] = pure $ Single x
toTree [x,y] = deep' mempty (One x) empty (One y)
toTree [x,y,z] = deep' mempty (Two x y) empty (One z)

toDigit :: Tuple v a -> Digit a
toDigit (Pair _ x y) = Two x y
toDigit (Triple _ x y z) = Three x y z

cons :: (MonadCredit m, Measured a v) => a -> FingerTree v a m -> m (FingerTree v a m)
cons x q = do
  tick
  case q of
    Empty -> pure $ Single x
    Single y -> do
      deep' mempty (One x) empty (One y)
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
      deep (measure z <> measure w <> vq) (Two x y) q' u

head :: MonadCredit m => FingerTree v a m -> m a
head Empty = fail "head: empty queue"
head (Single x) = pure x
head (Deep _ s _ _) = pure $ let (h:_) = toList s in h

tail :: (MonadCredit m, Measured a v) => FingerTree v a m -> m (FingerTree v a m)
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
      when (isTwo u) $
        q `creditWith` 1
      force q >>= (`deep0` u)

deep0 :: (MonadCredit m, Measured a v) => FingerTree v (Tuple v a) m -> Digit a -> m (FingerTree v a m)
deep0 Empty u = toTree $ toList u
deep0 (Single (Pair _ x y)) u = do
  deep' mempty (Two x y) empty u
deep0 (Single (Triple _ x y z)) u = do
  deep' (measure y <> measure z) (One x) (value (Single (pair y z))) u
deep0 (Deep vq pr q sf) u = do
  case chop0 pr of
    Left (x, y, vpr') -> do
      t <- delay $ FTail (Deep vq pr q sf)
      unless (isTwo u) $ creditWith t 1
      deep (vpr' <> vq <> measure sf) (Two x y) t u
    Right (x, pr'') -> do
      deep' (measure pr'' <> vq <> measure sf) (One x) (value (Deep vq pr'' q sf)) u

chop0 :: (Measured a v) => Digit (Tuple v a) -> Either (a, a, v) (a, Digit (Tuple v a))
chop0 (One (Pair _ x y)) = Left (x, y, mempty)
chop0 (Two (Pair _ x y) z) = Left (x, y, measure z)
chop0 (Three (Pair _ x y) z w) = Left (x, y, measure z <> measure w)
chop0 (One (Triple _ x y z)) = Right (x, One (pair y z))
chop0 (Two (Triple _ x y z) w) = Right (x, Two (pair y z) w)
chop0 (Three (Triple _ x y z) w u) = Right (x, Three (pair y z) w u)

uncons :: (MonadCredit m, Measured a v) => FingerTree v a m -> m (Maybe (a, FingerTree v a m))
uncons q =
  if isEmpty q
    then pure Nothing
    else do
      h <- head q
      t <- tail q
      pure $ Just (h, t)

deepL :: (MonadCredit m, Measured a v) => [a] -> v -> Thunk m (FLazyCon m) (FingerTree v (Tuple v a) m) -> Digit a -> m (FingerTree v a m)
deepL [] _ m sf = do
  m' <- uncons =<< force m
  case m' of
    Nothing -> toTree $ toList sf
    Just (Pair _ x y, m'') -> do
      deep' (measure m'') (Two x y) (value m'') sf
    Just (Triple _ x y z, m'') -> do
      deep' (measure m'') (Three x y z) (value m'') sf
deepL [x] vm m sf = deep vm (One x) m sf
deepL [x,y] vm m sf = deep vm (Two x y) m sf
deepL [x,y,z] vm m sf = deep vm (Three x y z) m sf

last :: (MonadCredit m, Measured a v) => FingerTree v a m -> m a
last Empty = fail "last: empty queue"
last (Single x) = pure x
last (Deep _ _ _ s) = pure $ let (h:_) = reverse $ toList s in h

snoc :: (MonadCredit m, Measured a v) => FingerTree v a m -> a -> m (FingerTree v a m)
snoc q w = do
  tick
  case q of
    Empty -> pure $ Single w
    Single x -> deep' mempty (One x) empty (One w)
    Deep vq u q (One x) ->
      deep vq u q (Two x w)
    Deep vq u q (Two x y) -> do
      q `creditWith` 1
      deep vq u q (Three x y w)
    Deep vq u q (Three x y z) -> do
      q' <- delay $ FSnoc q (pair x y)
      if isTwo u
        then q  `creditWith` 1
        else q' `creditWith` 1
      deep (vq <> measure x <> measure y) u q' (Two z w)

init :: (MonadCredit m, Measured a v) => FingerTree v a m -> m (FingerTree v a m)
init q = do
  tick
  case q of
    Empty -> pure Empty
    Single _ -> pure Empty
    Deep vq u q (Three x y _) -> do
      deep vq u q (Two x y)
    Deep vq u q (Two x _) -> do
      q `creditWith` 1
      deep vq u q (One x)
    Deep _ u q (One _) -> do
      when (isTwo u) $
        q `creditWith` 1
      deepN u =<< force q

deepN :: (MonadCredit m, Measured a v) => Digit a -> FingerTree v (Tuple v a) m -> m (FingerTree v a m)
deepN s Empty = toTree $ toList s
deepN s (Single (Pair _ x y)) = do
  deep' mempty s empty (Two x y)
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

unsnoc :: (MonadCredit m, Measured a v) => FingerTree v a m -> m (Maybe (FingerTree v a m, a))
unsnoc q =
  if isEmpty q
    then pure Nothing
    else do
      h <- last q
      t <- init q
      pure $ Just (t, h)

deepR :: (MonadCredit m, Measured a v) => Digit a -> v -> Thunk m (FLazyCon m) (FingerTree v (Tuple v a) m) -> [a] -> m (FingerTree v a m)
deepR s _ m [] = do
  m' <- unsnoc =<< force m
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

glue :: (MonadCredit m, Measured a v) => FingerTree v a m -> [a] -> FingerTree v a m -> m (FingerTree v a m)
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

concat' :: (MonadCredit m, Measured a v) => FingerTree v a m -> FingerTree v a m -> m (FingerTree v a m)
concat' q1 q2 = glue q1 [] q2

data Split v a m = Split
  { smaller :: FingerTree v a m
  , found   :: a
  , bigger  :: FingerTree v a m
  }

splitDigit :: Measured a v => (v -> Bool) -> v -> Digit a -> ([a], a, [a])
splitDigit p i (One x) = ([], x, [])
splitDigit p i (Two x y)
  | p (i <> measure x) = ([], x, [y])
  | otherwise = ([x], y, [])
splitDigit p i (Three x y z)
  | p (i <> measure x) = ([], x, [y, z])
  | p (i <> measure x <> measure y) = ([x], y, [z])
  | otherwise = ([x, y], z, [])

splitTree :: (MonadCredit m, Measured a v) => (v -> Bool) -> v -> FingerTree v a m -> m (Split v a m)
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

split :: (MonadCredit m, Measured a v) => (v -> Bool) -> FingerTree v a m -> m (FingerTree v a m, FingerTree v a m)
split p Empty = pure (Empty, Empty)
split p xs = do
  if p (measure xs)
    then do (Split l x r) <- splitTree p mempty xs
            (l,) <$> cons x r
    else pure (xs, Empty)

takeUntil :: (MonadCredit m, Measured a v) => (v -> Bool) -> FingerTree v a m -> m (FingerTree v a m)
takeUntil p m = fst <$> split p m

dropUntil :: (MonadCredit m, Measured a v) => (v -> Bool) -> FingerTree v a m -> m (FingerTree v a m)
dropUntil p m = snd <$> split p m

lookupTree :: (MonadCredit m, Measured a v) => (v -> Bool) -> v -> FingerTree v a m -> m (Maybe (v, a))
lookupTree p i Empty = pure Nothing
lookupTree p i t = do
  (Split l x _) <- splitTree p i t
  let ml = measure l
  pure $ Just (i <> ml, x)

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

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (FingerTree v a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Single a) = do
    a' <- prettyCell a
    pure $ mkMCell "Single" [a']
  prettyCell (Deep _ s q u) = do
    s' <- prettyCell s
    q' <- prettyCell q
    u' <- prettyCell u
    pure $ mkMCell "Deep" [s', q', u']

instance Pretty a => MemoryStructure (FingerTree v (PrettyCell a)) where
  prettyStructure = prettyCell

newtype Elem a = Elem a
  deriving (Eq, Ord, Show)

instance (MemoryCell m a) => MemoryCell m (Elem a) where
  prettyCell (Elem x) = prettyCell x

-- Deque

instance Measured (Elem a) () where
  measure (Elem x) = ()

newtype FingerDeque a m = FingerDeque (FingerTree () (Elem a) m)

instance D.Deque FingerDeque where
  empty = pure $ FingerDeque Empty
  cons x (FingerDeque q) = FingerDeque <$> cons (Elem x) q
  snoc (FingerDeque q) x = FingerDeque <$> snoc q (Elem x)
  uncons (FingerDeque q) = do
    m <- uncons q
    case m of
      Nothing -> pure Nothing
      Just (Elem x, q') -> pure $ Just (x, FingerDeque q')
  unsnoc (FingerDeque q) = do
    m <- unsnoc q
    case m of
      Nothing -> pure Nothing
      Just (q', Elem x) -> pure $ Just (FingerDeque q', x)
  concat (FingerDeque q1) (FingerDeque q2) = FingerDeque <$> concat' q1 q2

instance D.BoundedDeque FingerDeque where
  qcost _ (D.Cons _) = 2
  qcost _ (D.Snoc _) = 2
  qcost _ D.Uncons = 4
  qcost _ D.Unsnoc = 2
  qcost n D.Concat = 5 * log2 n

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (FingerDeque a m) where
  prettyCell (FingerDeque q) = prettyCell q

instance Pretty a => MemoryStructure (FingerDeque (PrettyCell a)) where
  prettyStructure = prettyCell

-- Random Access

newtype Size = Size Int
  deriving (Eq, Ord, Show, Num)

instance Semigroup Size where
  x <> y = x + y

instance Monoid Size where
  mempty = 0

instance Measured (Elem a) Size where
  measure (Elem x) = 1

newtype FingerRA a m = FingerRA (FingerTree Size (Elem a) m)

len :: MonadCredit m => FingerRA a m -> Size
len (FingerRA t) = measure t

splitAt :: MonadCredit m => Int -> FingerRA a m -> m (FingerRA a m, FingerRA a m)
splitAt i (FingerRA xs) = do
   (l, r) <- split (fromIntegral i <) xs
   pure $ (FingerRA l, FingerRA r)

instance RA.RandomAccess FingerRA where
  empty = pure $ FingerRA Empty
  cons x (FingerRA q) = FingerRA <$> cons (Elem x) q
  uncons (FingerRA q) = do
    m <- uncons q
    case m of
      Nothing -> pure Nothing
      Just (Elem x, m') -> do
        pure $ Just (x, FingerRA m')
  lookup i (FingerRA Empty) = pure Nothing
  lookup i (FingerRA xs) = do
    Split _ (Elem x) _ <- splitTree (fromIntegral i <) 0 xs
    pure $ Just x
  update i a (FingerRA Empty) = pure $ FingerRA Empty
  update i a (FingerRA xs) = do
    Split l (Elem x) r <- splitTree (fromIntegral i <) 0 xs
    if fromIntegral i > len (FingerRA l)
      then FingerRA <$> snoc l (Elem x)
      else FingerRA <$> (concat' l =<< cons (Elem a) r)

instance RA.BoundedRandomAccess FingerRA where
  qcost n (RA.Cons _) = 2
  qcost n RA.Uncons = 2
  qcost n (RA.Lookup i) = 5 * log2 n
  qcost n (RA.Update i _) = 2 + 10 * log2 n

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (FingerRA a m) where
  prettyCell (FingerRA q) = prettyCell q

instance Pretty a => MemoryStructure (FingerRA (PrettyCell a)) where
  prettyStructure = prettyCell

-- Heap

data Prio a = MInfty | Prio a
  deriving (Eq, Ord, Show)

instance Ord a => Semigroup (Prio a) where
  MInfty <> p = p
  p <> MInfty = p
  Prio x <> Prio y = Prio (min x y)

instance Ord a => Monoid (Prio a) where
  mempty = MInfty

instance Ord a => Measured (Elem a) (Prio a) where
  measure (Elem x) = Prio x

newtype FingerHeap a m = FingerHeap (FingerTree (Prio a) (Elem a) m)

instance H.Heap FingerHeap where
  empty = pure $ FingerHeap Empty
  insert x (FingerHeap xs) = FingerHeap <$> cons (Elem x) xs
  merge (FingerHeap a) (FingerHeap b) = FingerHeap <$> concat' a b
  splitMin (FingerHeap Empty) = pure Nothing
  splitMin (FingerHeap xs) = do
    (Split l (Elem x) r) <- splitTree (measure xs >=) mempty xs -- 3 * log n
    lr <- concat' l r -- 5 log n
    pure $ Just (x, FingerHeap lr)

instance H.BoundedHeap FingerHeap where
  hcost n (H.Insert _) = 2
  hcost n H.Merge = 5 * log2 n
  hcost n H.SplitMin = 1 + 10 * log2 (n + 1)

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (FingerHeap a m) where
  prettyCell (FingerHeap q) = prettyCell q

instance Pretty a => MemoryStructure (FingerHeap (PrettyCell a)) where
  prettyStructure = prettyCell

-- Sortable Collection

data Key a = NoKey | Key a
  deriving (Eq, Ord, Show)

instance Semigroup (Key a) where
  k <> NoKey = k
  _ <> k = k

instance Monoid (Key a) where
  mempty = NoKey

instance Eq a => Measured (Elem a) (Key a) where
  measure (Elem x) = Key x

newtype FingerSort a m = FingerSort (FingerTree (Key a) (Elem a) m)

rev :: MonadCredit m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc) 

append :: MonadCredit m => [a] -> [a] -> m [a]
append [] ys = pure ys
append (x : xs) ys = tick >> fmap (x:) (append xs ys)

treeToList :: MonadCredit m => [b] -> (a -> m [b]) -> FingerTree v a m -> m [b]
treeToList acc f Empty = rev acc []
treeToList acc f (Single x) = do
  fx <- f x
  flip rev [] =<< append fx acc
treeToList acc f (Deep _ s q u) = do
  s' <- fmap (concatMap id) $ traverse f $ toList s
  u' <- fmap (concatMap id) $ traverse f $ toList u
  creditWith q 2
  q' <- treeToList (u' ++ acc) (fmap (concatMap id) . traverse f . toList . toDigit) =<< force q
  append s' q'

instance S.Sortable FingerSort where
  empty = pure $ FingerSort Empty
  add x (FingerSort xs) = do
    (l, r) <- split (>= Key x) xs
    lxr <- concat' l =<< cons (Elem x) r
    pure $ FingerSort lxr
  sort (FingerSort xs) = do
    treeToList [] (\(Elem x) -> tick >> pure [x]) xs

instance S.BoundedSortable FingerSort where
  scost n (S.Add _) = 1 + 10 * log2 (n + 1)
  scost n S.Sort = 2 * log2 n + 3 * linear n

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (FingerSort a m) where
  prettyCell (FingerSort q) = prettyCell q

instance Pretty a => MemoryStructure (FingerSort (PrettyCell a)) where
  prettyStructure = prettyCell