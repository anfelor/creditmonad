{-# LANGUAGE GADTs, LambdaCase, QuantifiedConstraints #-}

module Test.Credit.Finger.FIP where

import Prelude hiding (head, tail, last, init)
import qualified Prelude
import Control.Monad (when, unless)
import Data.Foldable (foldlM, foldrM)
import Prettyprinter (Pretty)

import Control.Monad.Credit
import Test.Credit (linear, log2)
import Test.Credit.Finger.Base (Measured(..), Split(..))
import qualified Test.Credit.Finger.Base as F

-- | Fully In-Place, k-ary, Lazy Finger Trees
--
-- Interface:
--
--   fip fun measure(t : finger<v,a> @ borrow) : v @ borrow
--
--   fbip(2) fun cons(a : a, t : finger<v,a>) : finger<v,a>
--   fbip fun uncons(t : finger<v,a>) : maybe2<a, finger<v,a>>
--   fip fun head(t : finger<v,a> @ borrow) : a @ borrow
--   fbip fun tail(t : finger<v,a>) : finger<v,a>
--   // ... and the same for snoc, unsnoc, last, and init
--
--   type split<v,a> = { smaller : finger<v,a>, found : a, bigger : finger<v,a> }
--   fun splitTree(p : (v -> bool), t : finger<v,a>) : split<v,a>
--   fbip(6) fun concat(t1 : finger<v,a>, t2 : finger<v,a>) : finger<v,a>

-- Why so much fbip? We need to pass space credits down the tree
-- but often end up discarding them.
-- Also, the stack space of cons/uncons/splitTree is logarithmic.
-- The stack space of concat itself is constant,
-- but it can discard nodes and calls cons/snoc.

-- | Space argument
--
-- FIP Finger Trees are parameterised by the block size k.
-- (Here, we choose k = 3 for simplicity)
-- All nodes are padded to size k + 1, where the extra element holds the measure.
-- Since each node also has a header, this gives us size k + 2 for each node.

-- The cons/snoc functions were written to ensure that we always
-- push full blocks into the tree, to keep the space overhead as low as possible.
-- What is the space overhead of this design?

-- First, lets prove that in a full k-ary tree, at least (k - 1)/k of the nodes are leaves.
-- We define nodes(h) and elems(h) for a full tree of height h as follows:
-- nodes(0) = 1, nodes(h + 1) = k*nodes(h) + 1
-- nodes(h) = (k^(1 + h) - 1)/(k - 1)

-- elems(0) = k, elems(h + 1) = k*elems(h)
-- elems(h) = k^(1 + h)

-- lim nodes(h)/elems(h) = 1/(k - 1)
-- Each leaf holds k elements, so leafs(h)/nodes(h) = (k - 1)/k

-- Let's look at the space overhead of the different designs.
-- We can largely ignore the Deep/Digit structures, since its overhead
-- is only logarithmic in the number of elements.

-- In Claessen's finger trees, cons/snoc push 'Pair's into the tree.
-- This design has:
-- - In each leaf: two elements + header + measure
-- - In each internal node: two links + header + measure
-- - 2-ary tree: half the nodes are leaves
-- - -> eight words for two elements
-- - -> 4x space usage, 25% occupied

-- In Hinze and Paterson's finger trees, cons/snoc push 'Triple's into the tree.
-- This design has:
-- - In each leaf: three elements + header + measure
-- - In each internal node: three links + header + measure
-- - 3-ary tree: 2/3 of the nodes are leaves
-- - -> 7.5 words for three elements
-- - -> 2.5x space usage, 40% occupied

-- In our k-ary finger trees, cons/snoc push k elements into the tree.
-- This design has:
-- - In each leaf: k elements + header + measure
-- - In each internal node: k links + header + measure
-- - k-ary tree: (k - 1)/k of the nodes are leaves
-- - -> k + 2 + (k + 2)/(k - 1) words for k elements
-- - -> Asymptotically, (k + 2)/(k - 1) space usage, (k - 1)/(k + 2) occupied
-- Example:
-- - for k = 3, we have 5/2 space usage, 40% occupied
-- - for k = 6, we have 8/5 space usage, 62.5% occupied
-- - for k = 14, we have 16/13 space usage, 81.25% occupied

-- If we also include the Deep/Digit structure, we get:
--   space(n) = n(k+2)/(k-1) + 3(k + 2)log(n)

-- This also explains why it is impossible to make splitTree fip.
-- Given a tree A = B ++ C, we need to split A into B and C.
-- But 2*space(n/2) - space(n) = O(log(n))
-- and we have to allocate a logarithmic amount in splitTree.
-- This is bound to happen whenever A is more space efficient
-- than B and C by virtue of being larger.

-- This part is specific to the block size k = 3

-- | Size 4 space credit
data Unit = Unit
  deriving (Eq, Ord, Show)

-- | Contains 1..k elements
data Block a p = One p a | Two p a a | Three p a a a
  deriving (Eq, Ord, Show)

instance (Measured a v, Measured p v) => Measured (Block a p) v where
  measure (One p a) = measure (p, a)
  measure (Two p a b) = measure (p, a, b)
  measure (Three p a b c) = measure (p, a, b, c)

type Digit a = Block a (Maybe (Block a ()))

blockToDigit :: Block a () -> Digit a
blockToDigit (One () a) = One Nothing a
blockToDigit (Two () a b) = Two Nothing a b
blockToDigit (Three () a b c) = Three Nothing a b c

-- | A digit is unsafe if push or pop can cause it to become empty or overflow.
isSafe :: Digit a -> Bool
isSafe (One Nothing _) = False
isSafe (Two (Just _) _ _) = False
isSafe _ = True

-- -- | Split one block into two: typically requires one allocation.
-- splitBlock2 :: Measured a v => (v -> Bool) -> v -> Block a () -> (Maybe (Block a ()), a, Maybe (Block a ()))
-- splitBlock2 p i (One () a) = (Nothing, a, Nothing)
-- splitBlock2 p i (Two () a b)
  -- | p (i <> measure a) = (Nothing, a, Just (One () b))
  -- | otherwise = (Just (One () a), b, Nothing)
-- splitBlock2 p i (Three () a b c)
  -- | p (i <> measure a) = (Nothing, a, Just (Two () b c))
  -- | p (i <> measure (a, b)) = (Just (One () a), b, Just (One () c))
  -- | otherwise = (Just (Two () a b), c)

-- -- | Split one digit into two: typically requires one allocation.
-- splitBlock1 :: Measured a v => (v -> Bool) -> v -> Block a (Block a ()) -> (Maybe (Block a ()), Either (a, Maybe (Digit a)) (Block a ()))
-- splitBlock1 p i (One p a)
  -- | p (i <> measure a) = (Nothing, Left (a, Nothing))
  -- | otherwise = (Just (One () a), Right p)
-- splitBlock1 p i (Two p a b)
  -- | p (i <> measure a) = (Nothing, Left (Two () a b))
  -- | p (i <> measure (a, b)) = (Just (One () a), Left (One () b))
  -- | otherwise = (Just (Two () a b), Right ())
-- splitBlock1 p i (Three p a b c)
  -- | p (i <> measure a) = (Nothing, Left (Three () a b c))
  -- | p (i <> measure (a, b)) = (Just (One () a), Left (Two () b c))
  -- | p (i <> measure (a, b, c)) = (Just (Two () a b), Left (One () c))
  -- | otherwise = (Just (Three () a b c), Right ())

-- | Pushing works as follows:
--   - If a block has less than k elements, it is safe.
--   - If a block has k elements, it is dangerous.
--     We need to push out the other block in the digit.
--   - If a block is full, we create a new node
-- This type should be unboxed.
data PushState a = Safe (Digit a) Unit | Dangerous (Block a ()) (Maybe (Block a ())) Unit | Full (Digit a) 
  deriving (Eq, Ord, Show)

pushBlock :: a -> Digit a -> Unit -> PushState a
pushBlock x (One p a) u = Safe (Two p x a) u
pushBlock x (Two p a b) u = Dangerous (Three () x a b) p u
pushBlock x (Three _ a b c) _ = Full (One (Just (Three () a b c)) x)

-- This type should be unboxed.
data PopState a = NowEmpty a (Maybe (Block a ())) Unit | Occupied a (Digit a)
  deriving (Eq, Ord, Show)

popBlock :: Digit a -> PopState a
popBlock (One p a) = NowEmpty a p Unit
popBlock (Two p a b) = Occupied a (One p b)
popBlock (Three _ a b c) = Occupied a (Two Nothing b c)

-- | Contains 2..k elements
data Node v a = Pair v a a | Triple v a a a
  deriving (Eq, Ord, Show)

instance Measured a v => Measured (Node v a) v where
  measure (Pair v _ _) = v
  measure (Triple v _ _ _) = v

revNode :: Measured a v => Node v a -> Node v a
revNode (Pair v a b) = Pair (measure (b, a)) b a
revNode (Triple v a b c) = Triple (measure (c, b, a)) c b a

nodeToDigit :: Node v a -> Digit a
nodeToDigit (Pair _ a b) = Two Nothing a b
nodeToDigit (Triple _ a b c) = Three Nothing a b c

blockToNode :: Measured a v => Block a () -> Node v a
blockToNode (Three () a b c) = Triple (measure (a, b, c)) a b c

-- This part is independent of the block size k

-- FIPness constraints:
-- - singleton may use one space credit
-- - pop needs to return a space credit with empty digit
-- - nodeToDigit may not use space credits
-- - toTree may use two space credits
-- - to make glue fip, we may never have fully filled digits

singleton :: Unit -> a -> Digit a
singleton _ x = One Nothing x

-- | Push takes a space credit and may return a node
push :: Measured a v => a -> Digit a -> Unit -> (Digit a, Maybe (Node v a, Unit))
push x d u = case pushBlock x d u of
  Safe d _ -> (d, Nothing)
  Dangerous d Nothing u -> (blockToDigit d, Nothing)
  Dangerous d (Just b) u -> (blockToDigit d, Just (blockToNode b, u))
  Full d -> (d, Nothing)

headDigit :: Digit a -> a
headDigit d = case popBlock d of
  NowEmpty x _ _ -> x
  Occupied x _ -> x

measureDigitTail :: Measured a v => Digit a -> v
measureDigitTail d = case popBlock d of
  NowEmpty _ p _ -> measure p
  Occupied _ d -> measure d

-- | Pop takes an element from the block.
-- If the resulting digit is empty, it will return a space credit.
pop :: Digit a -> (a, Either Unit (Digit a))
pop d = case popBlock d of
    Occupied x d -> (x, Right d)
    NowEmpty x Nothing u -> (x, Left u) -- return space credit
    NowEmpty x (Just back) u -> (x, Right (blockToDigit back)) -- could return space credit

-- TODO: we call this on both pr and sf, but this does not respect the reversed order of sf
toTree :: (MonadCredit m, Measured a v) => (Unit, Unit) -> Digit a -> m (FIP v a m)
toTree (u1, u2) d = case popBlock d of
  Occupied a d -> deep' mempty (singleton u1 a) vempty d u2
  NowEmpty a Nothing u3 -> pure $ Single a
  NowEmpty a (Just back) u3 -> deep' mempty (singleton u1 a) vempty (blockToDigit back) u2

-- | Pad all to four elements
data FIP v a m
  = Empty
  | Single a
  | Deep v (Digit a) (Thunk m (FLazyCon m) (FIP v (Node v a) m)) (Digit a)

data FLazyCon m a where
  FCons :: Measured a v => a -> Thunk m (FLazyCon m) (FIP v a m) -> FLazyCon m (FIP v a m)
  FSnoc :: Measured a v => Thunk m (FLazyCon m) (FIP v a m) -> a -> FLazyCon m (FIP v a m)
  FDeepL :: Measured a v => v -> Unit -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Digit a -> FLazyCon m (FIP v a m)
  FDeepR :: Measured a v => v -> Digit a -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Unit -> FLazyCon m (FIP v a m)

instance MonadCredit m => HasStep (FLazyCon m) m where
  -- We get a space credit from the thunk
  step (FCons x m) = cons Unit x =<< force m
  step (FSnoc m x) = flip (snoc Unit) x =<< force m
  step (FDeepL v u m sf) = deepL (Unit, u) Nothing v m sf
  step (FDeepR v pr m u) = deepR (Unit, u) pr v m Nothing

instance Measured a v => Measured (FIP v a m) v where
  measure Empty = mempty
  measure (Single x) = measure x
  measure (Deep vm f m r) = measure f <> vm <> measure r

instance F.FingerTree FIP where
  empty = Empty
  isEmpty Empty = True
  isEmpty _ = False

  cons = cons Unit
  head = head
  tail = tail

  snoc = snoc Unit
  last = last
  init = init

  concat q1 q2 = fail "concat not implemented" -- glue q1 [] q2
  splitTree _ _ _ = fail "splitTree not implemented" -- splitTree
  treeToList q = treeToListAcc [] (\x -> [x]) q

-- Amortization idea:
--  - FCons and FSnoc both cost two credits
--  - FDeepL and FDeepR both cost three credits
--  - the first credit is used to tick
--  - We maintain the invariant:
--    - The m thunk requires two credits to force.
--    - In each queue Deep(f, m, r), m has ||f| - 2| + ||r| - 2| credits.
--  - snoc and tail spend their second credit on either the old m to be able to force it,
--    or on the new m to maintain the invariant.

instance F.BoundedFingerTree FIP where
  fcost _ F.Cons = 2
  fcost _ F.Head = 0
  fcost _ F.Tail = 4
  fcost _ F.Snoc = 2
  fcost _ F.Last = 0
  fcost _ F.Init = 4
  fcost n F.Concat = 5 * log2 n
  fcost n F.SplitTree = 5 * log2 n
  fcost n F.TreeToList = 2 * log2 n + 3 * linear n

vempty :: MonadCredit m => m (Thunk m (FLazyCon m) (FIP v a m))
vempty = value Empty

deep :: (MonadCredit m, Measured a v) => v -> Digit a -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Digit a -> Unit -> m (FIP v a m)
deep v f m r _ = do
  let dang d = if isSafe d then 0 else 1
  m `hasAtLeast` (dang f + dang r)
  lazymatch m (\m -> when (v /= measure m) $ error "invalid measure") (\_ -> pure ())
  pure $ Deep v f m r

deep' :: (MonadCredit m, Measured a v) => v -> Digit a -> m (Thunk m (FLazyCon m) (FIP v (Node v a) m)) -> Digit a -> Unit -> m (FIP v a m)
deep' vm f mkM r u = do
  m <- mkM
  deep vm f m r u

cons :: (MonadCredit m, Measured a v) => Unit -> a -> FIP v a m -> m (FIP v a m)
cons u1 a q = do
  tick
  case q of
    Empty -> pure $ Single a
    Single b -> do
      -- In this case, we need one extra allocation.
      -- It seems hard to avoid this: in a previous approach, we would store a unit on Single
      -- but that requires us to box the empty type, which creates a fourth allocation here.
      deep' mempty (singleton u1 a) vempty (singleton Unit b) Unit
    Deep vm pr m sf ->
      case push a pr Unit of -- Unit from Deep
        (pr', Nothing) -> do
          m `creditWith` 1
          deep vm pr' m sf u1
        (pr', Just (node, u)) -> do
          m' <- delay $ FCons node m -- at u
          if isSafe sf
            then m  `creditWith` 1
            else m' `creditWith` 1
          deep (measure node <> vm) pr' m' sf u1

head :: MonadCredit m => FIP v a m -> m a
head Empty = fail "head: empty queue"
head (Single x) = pure x
head (Deep _ pr _ _) = pure $ headDigit pr

uncons :: (MonadCredit m, Measured a v) => FIP v a m -> m (Maybe (a, Thunk m (FLazyCon m) (FIP v a m)))
uncons q = do
  tick
  case q of
    Empty -> pure $ Nothing
    Single a -> do
      e <- vempty
      pure $ Just (a, e)
    Deep vm pr m sf -> do
      case pop pr of
        (a, Left u) -> do
          t <- delay $ FDeepL vm u m sf -- at Deep
          t `creditWith` 1
          pure $ Just (a, t)
        (a, Right pr') -> do
          m `creditWith` 1
          t <- deep vm pr' m sf Unit -- from Deep
          t' <- value t
          pure $ Just (a, t')

tail :: (MonadCredit m, Measured a v) => FIP v a m -> m (FIP v a m)
tail q = do
  m <- uncons q
  case m of
    Nothing -> pure Empty
    Just (_, t) -> do
      t `creditWith` 2
      force t

deepL :: (MonadCredit m, Measured a v) => (Unit, Unit) -> Maybe (Digit a) -> v -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Digit a -> m (FIP v a m)
deepL (u1, u2) Nothing _ m sf = do
  when (isSafe sf) $ m `creditWith` 1
  m' <- force m
  let mt = measureTail m'
  m'' <- uncons m'
  case m'' of
    Nothing -> toTree (u1, u2) sf
    Just (h, t) -> do -- h is safe
      unless (isSafe sf) $ t `creditWith` 1
      deep mt (nodeToDigit h) t sf u2
deepL (u1, _) (Just pr) vm m sf = deep vm pr m sf u1

-- | FIP if it takes its argument as borrowed and returns int
measureTail :: Measured a v
            => FIP v (Node v a) m -> v
measureTail q = case q of
  Empty -> mempty
  Single _ -> mempty
  Deep v pr _ sf -> measureDigitTail pr <> v <> measure sf

snoc :: (MonadCredit m, Measured a v)
     => Unit -> FIP v a m -> a -> m (FIP v a m)
snoc u1 q e = do
  tick
  case q of
    Empty -> pure $ Single e -- at u1
    Single a -> do
      -- Needs extra allocation, see 'cons'
      deep' mempty (singleton u1 a) vempty (singleton Unit e) Unit
    Deep vm pr m sf ->
      case push e sf Unit of -- from Deep
        (sf', Nothing) -> do
          m `creditWith` 1
          deep vm pr m sf' u1
        (sf', Just (node, u)) -> do
          t <- delay $ FSnoc m (revNode node) -- at u
          if isSafe pr
            then m `creditWith` 1
            else t `creditWith` 1
          deep (vm <> measure node) pr t sf' u1

last :: (MonadCredit m, Measured a v) => FIP v a m -> m a
last Empty = fail "last: empty queue"
last (Single x) = pure x
last (Deep _ _ _ sf) = pure $ headDigit sf

unsnoc :: (MonadCredit m, Measured a v) => FIP v a m -> m (Maybe (Thunk m (FLazyCon m) (FIP v a m), a))
unsnoc q = do
  tick
  case q of
    Empty -> pure $ Nothing
    Single a -> do
      e <- vempty
      pure $ Just (e, a)
    Deep vm pr m sf ->
      case pop sf of
        (a, Left u) -> do
          t <- delay $ FDeepR vm pr m u -- from Deep
          t `creditWith` 1
          pure $ Just (t, a)
        (a, Right sf') -> do
          m `creditWith` 1
          t <- deep vm pr m sf' Unit -- from Deep
          t' <- value t
          pure $ Just (t', a)

init :: (MonadCredit m, Measured a v) => FIP v a m -> m (FIP v a m)
init q = do
  m <- unsnoc q
  case m of
    Nothing -> pure Empty
    Just (t, _) -> do
      t `creditWith` 2
      force t

deepR :: (MonadCredit m, Measured a v) => (Unit, Unit) -> Digit a -> v -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Maybe (Digit a) -> m (FIP v a m)
deepR (u1, u2) pr _ m Nothing = do
  when (isSafe pr) $ m `creditWith` 1
  m' <- force m
  let mi = measureInit m'
  m'' <- unsnoc m'
  case m'' of
    Nothing -> toTree (u1, u2) pr
    Just (t, l) -> do -- l is safe
      unless (isSafe pr) $ t `creditWith` 1
      deep mi pr t (nodeToDigit (revNode l)) u2
deepR (u1, _) s vm m (Just sf) = deep vm s m sf u1

measureInit :: Measured a v
            => FIP v (Node v a) m -> v
measureInit q = case q of
  Empty -> mempty
  Single _ -> mempty
  Deep v pr _ sf -> measure pr <> v <> measureDigitTail sf

-- To make glue fip, we do the following:
-- - The cons cells of the middle list are padded to size k
-- - The middle list contains at most 5 nodes
-- - This is preserved, since every recursive call we add at most 4k - 2 elements
--   and then group them by k. So (4k + 3) / k = 4 + 3/k <= 5
-- - In the base case, we need to allocate to cons/snoc
--   but this is at most five allocations by the above result
--
-- This design tries to "repair" allocations by making the internal node as big as possible.
-- In particular, if (Split l x r = splitTree p i t), then `concat l r` and `concat l (cons x r)`
-- try to restore the original tree t.

-- toNodes :: Measured a v => [a] -> [Node v a]
-- toNodes [] = []
-- toNodes [x, y] = [pair x y]
-- toNodes [x, y, z, w] = [pair x y, pair z w]
-- toNodes (x : y : z : xs) = triple x y z : toNodes xs

-- -- | Needs five allocations in the base case to cons/snoc.
-- glue :: (MonadCredit m, Measured a v) => FIP v a m -> [a] -> FIP v a m -> m (FIP v a m)
-- glue Empty as q2 = foldrM (cons Unit) q2 as
-- glue q1 as Empty = foldlM (snoc Unit) q1 as
-- glue (Single x) as q2 = do 
  -- q <- foldrM (cons Unit) q2 as
  -- cons Unit x q -- from Single
-- glue q1 as (Single y) = do
  -- q <- foldlM (snoc Unit) q1 as
  -- snoc Unit q y -- from Single
-- glue (Deep _ u1 q1 v1) as (Deep _ u2 q2 v2) = tick >> do
  -- creditWith q1 2
  -- q1 <- force q1
  -- creditWith q2 2
  -- q2 <- force q2
  -- q <- glue q1 (toNodes (v1 ++ as ++ u2)) q2
  -- deep' (measure q) u1 (value q) v2 -- from first Deep

-- -- | 'Split' should be padded to size k
-- splitTree :: (MonadCredit m, Measured a v) => (v -> Bool) -> v -> FIP v a m -> m (Split FIP v a m)
-- splitTree p i Empty = fail "splitTree: empty tree"
-- splitTree p i (Single x) = pure $ Split Empty x Empty -- from Single
-- splitTree p i (Deep vm pr m sf) = do
  -- tick
  -- m `creditWith` 2
  -- let vpr = i <> measure pr
  -- let vprm = vpr <> vm
  -- if p vpr then do
    -- let (l, x, r) = splitDigit p i pr
    -- Split <$> toTree (Unit, Unit) l <*> pure x <*> deepL (Unit, Unit) r vm m sf
  -- else if p vprm then do
    -- Split ml xs mr <- splitTree p vpr =<< force m
    -- let vml = measure ml
    -- let (l, x, r) = splitDigit p (vpr <> vml) (toDigit xs)
    -- [ml', mr'] <- mapM value [ml, mr]
    -- Split <$> deepR pr vml ml' l <*> pure x <*> deepL r (measure mr) mr' sf
  -- else do
    -- let (l, x, r) = splitDigit p vprm sf
    -- Split <$> deepR pr vm m l <*> pure x <*> toTree r

append :: MonadCredit m => [a] -> [a] -> m [a]
append [] ys = pure ys
append (x : xs) ys = tick >> fmap (x:) (append xs ys)

blockToList :: Block a () -> [a]
blockToList (One () a) = [a]
blockToList (Two () a b) = [a, b]
blockToList (Three () a b c) = [a, b, c]

digitToList :: Digit a -> [a]
digitToList (One p a) = [a] ++ maybe [] blockToList p
digitToList (Two p a b) = [a, b] ++ maybe [] blockToList p
digitToList (Three p a b c) = [a, b, c] ++ maybe [] blockToList p

nodeToList :: Node v a -> [a]
nodeToList (Pair _ a b) = [a, b]
nodeToList (Triple _ a b c) = [a, b, c]

treeToListAcc :: MonadCredit m => [b] -> (a -> [b]) -> FIP v a m -> m [b]
treeToListAcc acc f Empty = pure acc
treeToListAcc acc f (Single x) = append (f x) acc
treeToListAcc acc f (Deep _ pr m sf) = do
  let pr' = concatMap f $ digitToList pr
  let sf' = concatMap f $ reverse $ digitToList sf
  acc' <- append sf' acc
  creditWith m 2
  m' <- treeToListAcc acc' (concatMap f . nodeToList) =<< force m
  append pr' m'

instance (MemoryCell m a, MemoryCell m p) => MemoryCell m (Block a p) where
  prettyCell (One p a) = do
    a' <- prettyCell a
    p' <- prettyCell p
    pure $ mkMCell "One" [p', a']
  prettyCell (Two p a b) = do
    a' <- prettyCell a
    b' <- prettyCell b
    p' <- prettyCell p
    pure $ mkMCell "Two" [p', a', b']
  prettyCell (Three p a b c) = do
    a' <- prettyCell a
    b' <- prettyCell b
    c' <- prettyCell c
    p' <- prettyCell p
    pure $ mkMCell "Three" [p', a', b', c']

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
  prettyCell (FDeepL v u m sf) = do
    -- m' <- prettyCell m
    -- sf' <- prettyCell sf
    pure $ mkMCell "FDeepL" []
  prettyCell (FDeepR v pr m u) = do
    -- pr' <- prettyCell pr
    -- m' <- prettyCell m
    pure $ mkMCell "FDeepR" []

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (FIP v a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Single a) = do
    a' <- prettyCell a
    pure $ mkMCell "Single" [a']
  prettyCell (Deep _ s q u) = do
    s' <- prettyCell s
    q' <- prettyCell q
    u' <- prettyCell u
    pure $ mkMCell "Deep" [s', q', u']

instance (forall m. Monad m => MemoryCell m a) => MemoryStructure (FIP v a) where
  prettyStructure = prettyCell