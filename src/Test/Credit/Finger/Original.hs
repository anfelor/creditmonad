{-# LANGUAGE GADTs, LambdaCase, QuantifiedConstraints #-}

module Test.Credit.Finger.Original where

import Prelude hiding (head, tail, last, init)
import qualified Prelude
import Control.Monad (when, unless)
import Data.Foldable (foldlM, foldrM)
import Prettyprinter (Pretty)

import Control.Monad.Credit
import Test.Credit (linear, log2)
import Test.Credit.Finger.Base (Measured(..), Split(..))
import qualified Test.Credit.Finger.Base as F

type Digit a = [a]

data Node v a = Pair v a a | Triple v a a a
  deriving (Eq, Ord, Show)

data Original v a m
  = Empty
  | Single a
  | Deep v (Digit a) (Thunk m (FLazyCon m) (Original v (Node v a) m)) (Digit a)

data FLazyCon m a where
  FCons :: Measured a v => a -> Thunk m (FLazyCon m) (Original v a m) -> FLazyCon m (Original v a m)
  FSnoc :: Measured a v => Thunk m (FLazyCon m) (Original v a m) -> a -> FLazyCon m (Original v a m)
  FTail :: Measured a v => Original v a m -> FLazyCon m (Original v a m)
  FInit :: Measured a v => Original v a m -> FLazyCon m (Original v a m)

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

instance (Eq v, Monoid v) => Measured (Node v a) v where
  measure (Pair v _ _) = v
  measure (Triple v _ _ _) = v

instance Measured a v => Measured (Original v a m) v where
  measure Empty = mempty
  measure (Single x) = measure x
  measure (Deep vm f m r) = measure f <> vm <> measure r

instance F.FingerTree Original where
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

instance F.BoundedFingerTree Original where
  fcost _ F.Cons = 2
  fcost _ F.Head = 0
  fcost _ F.Tail = 2
  fcost _ F.Snoc = 2
  fcost _ F.Last = 0
  fcost _ F.Init = 2
  fcost n F.Concat = 5 * log2 n
  fcost n F.SplitTree = 5 * log2 n
  fcost n F.TreeToList = 2 * log2 n + 3 * linear n

isSafe :: Digit a -> Bool
isSafe [_,_] = True
isSafe [_,_,_] = True
isSafe _ = False

vempty :: MonadCredit m => m (Thunk m (FLazyCon m) (Original v a m))
vempty = value $ Empty

pair :: Measured a v => a -> a -> Node v a
pair x y = Pair (measure x <> measure y) x y

triple :: Measured a v => a -> a -> a -> Node v a
triple x y z = Triple (measure x <> measure y <> measure z) x y z

deep :: (MonadCredit m, Measured a v) => v -> Digit a -> Thunk m (FLazyCon m) (Original v (Node v a) m) -> Digit a -> m (Original v a m)
deep v f m r = do
  let dang d = if isSafe d then 0 else 1
  m `hasAtLeast` (dang f + dang r)
  lazymatch m (\m -> when (v /= measure m) $ error "invalid measure") (\_ -> pure ())
  pure $ Deep v f m r

deep' :: (MonadCredit m, Measured a v) => v -> Digit a -> m (Thunk m (FLazyCon m) (Original v (Node v a) m)) -> Digit a -> m (Original v a m)
deep' vm f mkM r = do
  m <- mkM
  deep vm f m r

toTree :: (MonadCredit m, Measured a v) => [a] -> m (Original v a m)
toTree [] = pure Empty
toTree [a] = pure $ Single a
toTree [a,b] = deep' mempty [a] vempty [b]
toTree [a,b,c] = deep' mempty [a,b] vempty [c]
toTree [a,b,c,d] = deep' mempty [a,b] vempty [c,d]

toDigit :: Node v a -> Digit a
toDigit (Pair _ x y) = [x, y]
toDigit (Triple _ x y z) = [x, y, z]

cons :: (MonadCredit m, Measured a v) => a -> Original v a m -> m (Original v a m)
cons a q = do
  tick
  case q of
    Empty -> pure $ Single a
    Single b -> do
      deep' mempty [a] vempty [b]
    Deep vm [b, c, d, e] m sf -> do
      m' <- delay $ FCons (triple c d e) m
      if isSafe sf
        then m  `creditWith` 1
        else m' `creditWith` 1
      deep (measure (c, d, e) <> vm) [a, b] m' sf
    Deep vm pr m sf -> do
      m `creditWith` 1
      deep vm ([a] ++ pr) m sf

head :: MonadCredit m => Original v a m -> m a
head Empty = fail "head: empty queue"
head (Single x) = pure x
head (Deep _ (h:_) _ _) = pure h

tail :: (MonadCredit m, Measured a v)
     => Original v a m -> m (Original v a m)
tail q = do
  tick
  case q of
    Empty -> pure Empty
    Single _ -> pure Empty
    Deep vq [_] q u -> do
      when (isSafe u) $ q `creditWith` 1
      deepL [] vq q u
    Deep vq (_:pr) q u -> do
      q `creditWith` 1
      deep vq pr q u

deepL :: (MonadCredit m, Measured a v) => [a] -> v -> Thunk m (FLazyCon m) (Original v (Node v a) m) -> Digit a -> m (Original v a m)
deepL [] _ m sf = do
  m' <- force m
  if F.isEmpty m'
    then toTree sf
    else do
      t <- delay $ FTail m'
      unless (isSafe sf) $ t `creditWith` 1
      h <- head m'
      deep (measureTail m') (toDigit h) t sf
deepL pr vm m sf = deep vm pr m sf

measureTail :: Measured a v
            => Original v (Node v a) m -> v
measureTail q = case q of
  Empty -> mempty
  Single _ -> mempty
  Deep v pr _ sf -> measure (Prelude.tail pr) <> v <> measure sf

snoc :: (MonadCredit m, Measured a v)
     => Original v a m -> a -> m (Original v a m)
snoc q e = do
  tick
  case q of
    Empty -> pure $ Single e
    Single a -> do
      deep' mempty [a] vempty [e]
    Deep v front middle [a,b,c,d] -> do
      t <- delay $ FSnoc middle (triple a b c)
      if isSafe front
        then middle `creditWith` 1
        else t      `creditWith` 1
      deep (v <> measure (a, b, c)) front t [d, e] 
    Deep v front middle sf -> do
      middle `creditWith` 1
      deep v front middle (sf ++ [e])

last :: (MonadCredit m, Measured a v) => Original v a m -> m a
last Empty = fail "last: empty queue"
last (Single x) = pure x
last (Deep _ _ _ s) = pure $ Prelude.last s

init :: (MonadCredit m, Measured a v) => Original v a m -> m (Original v a m)
init q = do
  tick
  case q of
    Empty -> pure Empty
    Single _ -> pure Empty
    Deep v f q [_] -> do
      when (isSafe f) $ q `creditWith` 1
      deepR f v q []
    Deep vq f q sf -> do
      q `creditWith` 1
      deep vq f q (Prelude.init sf)

deepR :: (MonadCredit m, Measured a v) => Digit a -> v -> Thunk m (FLazyCon m) (Original v (Node v a) m) -> [a] -> m (Original v a m)
deepR pr _ m [] = do
  m' <- force m
  if F.isEmpty m'
    then toTree pr
    else do
      t <- delay $ FInit m'
      unless (isSafe pr) $ t `creditWith` 1
      l <- last m'
      deep (measureInit m') pr t (toDigit l)
deepR s vm m sf = deep vm s m sf

measureInit :: Measured a v
            => Original v (Node v a) m -> v
measureInit q = case q of
  Empty -> mempty
  Single _ -> mempty
  Deep v pr _ sf -> measure pr <> v <> measure (Prelude.init sf)

toNodes :: Measured a v => [a] -> [Node v a]
toNodes [] = []
toNodes [x, y] = [pair x y]
toNodes [x, y, z, w] = [pair x y, pair z w]
toNodes (x : y : z : xs) = triple x y z : toNodes xs

glue :: (MonadCredit m, Measured a v) => Original v a m -> [a] -> Original v a m -> m (Original v a m)
glue Empty as q2 = foldrM cons q2 as
glue q1 as Empty = foldlM snoc q1 as
glue (Single x) as q2 = foldrM cons q2 (x : as)
glue q1 as (Single y) = foldlM snoc q1 (as ++ [y])
glue (Deep _ u1 q1 v1) as (Deep _ u2 q2 v2) = tick >> do
  creditWith q1 2
  q1 <- force q1
  creditWith q2 2
  q2 <- force q2
  q <- glue q1 (toNodes (v1 ++ as ++ u2)) q2
  deep' (measure q) u1 (value q) v2

splitDigit :: Measured a v => (v -> Bool) -> v -> Digit a -> ([a], a, [a])
splitDigit p i [x] = ([], x, [])
splitDigit p i [x, y] 
  | p (i <> measure x) = ([], x, [y])
  | otherwise = ([x], y, [])
splitDigit p i [x, y, z]
  | p (i <> measure x) = ([], x, [y, z])
  | p (i <> measure x <> measure y) = ([x], y, [z])
  | otherwise = ([x, y], z, [])
splitDigit p i [a, b, c, d]
  | p (i <> measure a) = ([], a, [b, c, d])
  | p (i <> measure a <> measure b) = ([a], b, [c, d])
  | p (i <> measure a <> measure b <> measure c) = ([a, b], c, [d])
  | otherwise = ([a, b, c], d, [])

splitTree :: (MonadCredit m, Measured a v) => (v -> Bool) -> v -> Original v a m -> m (Split Original v a m)
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

append :: MonadCredit m => [a] -> [a] -> m [a]
append [] ys = pure ys
append (x : xs) ys = tick >> fmap (x:) (append xs ys)

treeToListAcc :: MonadCredit m => [b] -> (a -> [b]) -> Original v a m -> m [b]
treeToListAcc acc f Empty = pure acc
treeToListAcc acc f (Single x) = append (f x) acc
treeToListAcc acc f (Deep _ s q u) = do
  let s' = concatMap f s
  let u' = concatMap f u
  acc' <- append u' acc
  creditWith q 2
  q' <- treeToListAcc acc' (concatMap f . toDigit) =<< force q
  append s' q'

instance MemoryCell m a => MemoryCell m (Node v a) where
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

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Original v a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Single a) = do
    a' <- prettyCell a
    pure $ mkMCell "Single" [a']
  prettyCell (Deep _ s q u) = do
    s' <- prettyCell s
    q' <- prettyCell q
    u' <- prettyCell u
    pure $ mkMCell "Deep" [s', q', u']

instance (forall m. Monad m => MemoryCell m a) => MemoryStructure (Original v a) where
  prettyStructure = prettyCell