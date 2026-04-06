{-# LANGUAGE GADTs, LambdaCase, QuantifiedConstraints, DataKinds, TypeFamilies, KindSignatures #-}

module Test.Credit.Finger.FIP where

import Prelude hiding (head, tail, last, init)
import Control.Monad (when, unless)

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
--   fbip fun cons(a : a, u : unit, t : finger<v,a>) : finger<v,a>
--   fbip fun uncons(t : finger<v,a>) : maybe2<a, finger<v,a>>
--   fip fun head(t : finger<v,a> @ borrow) : a @ borrow
--   fbip fun tail(t : finger<v,a>) : finger<v,a>
--   // ... and the same for snoc, unsnoc, last, and init
--
--   type split<v,a> = { smaller : finger<v,a>, found : a, bigger : finger<v,a> }
--   fun splitTree(p : (v -> bool), t : finger<v,a>) : split<v,a>
--   fbip(k + 5) fun concat(t1 : finger<v,a>, t2 : finger<v,a>) : finger<v,a>

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

-- This part is specific to the block size k = 5

-- | Size 6 space credit
data Unit = Unit
  deriving (Eq, Ord, Show)

-- | Contains 1..k elements, stored in reverse order
data Block a p = One p a | Two p a a | Three p a a a | Four p a a a a | Five p a a a a a
  deriving (Eq, Ord, Show)

instance (Measured a v, Measured p v) => Measured (Block a p) v where
  measure (One p a) = measure (a, p)
  measure (Two p b a) = measure (a, b, p)
  measure (Three p c b a) = measure (a, b, c, p)
  measure (Four p d c b a) = measure (a, b, c, d, p)
  measure (Five p e d c b a) = measure (a, b, c, d, e, p)

blockToList :: Block a () -> [a]
blockToList (One () a) = [a]
blockToList (Two () b a) = [a, b]
blockToList (Three () c b a) = [a, b, c]
blockToList (Four () d c b a) = [a, b, c, d]
blockToList (Five () e d c b a) = [a, b, c, d, e]

data Orientation = Ordered | Flipped

type family Flip (o :: Orientation) :: Orientation where
  Flip 'Ordered = 'Flipped
  Flip 'Flipped = 'Ordered

newtype Digit (o :: Orientation) a = Digit { unDigit :: Block a (Maybe (Block a ())) }
  deriving (Eq, Ord, Show)

instance (Measured a v) => Measured (Digit 'Ordered a) v where
  measure = measure . unDigit

mkDigit :: Block a () -> Maybe (Block a ()) -> Digit o a
mkDigit b Nothing = Digit $ addBlock Nothing b
mkDigit b (Just m) =
  let (b', m') = shiftL b m
  in case (b', m') of
    (Nothing, Just m') -> Digit $ addBlock Nothing m'
    (Just b', m') -> Digit $ addBlock m' b'

addBlock :: p -> Block a () -> Block a p
addBlock m (One () a) = One m a
addBlock m (Two () b a) = Two m b a
addBlock m (Three () c b a) = Three m c b a
addBlock m (Four () d c b a) = Four m d c b a
addBlock m (Five () e d c b a) = Five m e d c b a

breakBlock :: Block a p -> (Block a (), p)
breakBlock (One m a) = (One () a, m)
breakBlock (Two m b a) = (Two () b a, m)
breakBlock (Three m c b a) = (Three () c b a, m)
breakBlock (Four m d c b a) = (Four () d c b a, m)
breakBlock (Five m e d c b a) = (Five () e d c b a, m)

flipBlock :: Block a () -> Block a ()
flipBlock (One () a) = One () a
flipBlock (Two () b a) = Two () a b
flipBlock (Three () c b a) = Three () a b c
flipBlock (Four () d c b a) = Four () a b c d
flipBlock (Five () e d c b a) = Five () a b c d e

flipDigit :: Digit o a -> Digit (Flip o) a
flipDigit d = let (b, m) = breakBlock (unDigit d) in go (flipBlock b) m
  where
    go b Nothing = blockToDigit b
    go b (Just m) = mkDigit (flipBlock m) (Just b)

-- | A digit is unsafe if push or pop can cause it to become empty or overflow.
isSafe :: Digit o a -> Bool
isSafe (Digit (One Nothing _)) = False
isSafe (Digit (Four (Just _) _ _ _ _)) = False
isSafe _ = True

-- | Split a block into two: requires up to one allocation.
splitBlock :: Measured a v => (v -> Bool) -> v -> Block a () -> (Maybe (Block a ()), a, Maybe (Block a ()))
splitBlock p i (One () a) = (Nothing, a, Nothing)
splitBlock p i (Two () b a)
  | p (i <> measure a) = (Nothing, a, Just (One () b))
  | otherwise = (Just (One () a), b, Nothing)
splitBlock p i (Three () c b a)
  | p (i <> measure a) = (Nothing, a, Just (Two () c b))
  | p (i <> measure (a, b)) = (Just (One () a), b, Just (One () c))
  | otherwise = (Just (Two () b a), c, Nothing)
splitBlock p i (Four () d c b a)
  | p (i <> measure a) = (Nothing, a, Just (Three () d c b))
  | p (i <> measure (a, b)) = (Just (One () a), b, Just (Two () d c))
  | p (i <> measure (a, b, c)) = (Just (Two () b a), c, Just (One () d))
  | otherwise = (Just (Three () c b a), d, Nothing)
splitBlock p i (Five () e d c b a)
  | p (i <> measure a) = (Nothing, a, Just (Four () e d c b))
  | p (i <> measure (a, b)) = (Just (One () a), b, Just (Three () e d c))
  | p (i <> measure (a, b, c)) = (Just (Two () b a), c, Just (Two () e d))
  | p (i <> measure (a, b, c, d)) = (Just (Three () c b a), d, Just (One () e))
  | otherwise = (Just (Four () d c b a), e, Nothing)

-- | Shift elements from the first into the second block.
-- Return up to one partly filled block and up to one fully filled block.
-- TODO: Can we have reduce the number of cases here?
shiftL :: Block a () -> Block a () -> (Maybe (Block a ()), Maybe (Block a ()))
shiftL (One () a) (Five () f e d c b) = (Just $ One () a, Just $ Five () f e d c b)
shiftL a (Five () f e d c b) = (Just a, Just $ Five () f e d c b)
shiftL (One () a) (One () b) = (Just $ Two () b a, Nothing)
shiftL (One () a) (Two () c b) = (Just $ Three () c b a, Nothing)
shiftL (One () a) (Three () d c b) = (Just $ Four () d c b a, Nothing)
shiftL (One () a) (Four () e d c b) = (Nothing, Just $ Five () e d c b a)
shiftL (Two () b a) (One () c) = (Just $ Three () c b a, Nothing)
shiftL (Two () b a) (Two () d c) = (Just $ Four () d c b a, Nothing)
shiftL (Two () b a) (Three () e d c) = (Nothing, Just $ Five () e d c b a)
shiftL (Two () b a) (Four () f e d c) = (Just $ One () a, Just $ Five () f e d c b)
shiftL (Three () c b a) (One () d) = (Just $ Four () d c b a, Nothing)
shiftL (Three () c b a) (Two () e d) = (Nothing, Just $ Five () e d c b a)
shiftL (Three () c b a) (Three () f e d) = (Just $ One () a, Just $ Five () f e d c b)
shiftL (Three () c b a) (Four () g f e d) = (Just $ Two () b a, Just $ Five () g f e d c)
shiftL (Four () d c b a) (One () e) = (Nothing, Just $ Five () e d c b a)
shiftL (Four () d c b a) (Two () f e) = (Just $ One () a, Just $ Five () f e d c b)
shiftL (Four () d c b a) (Three () g f e) = (Just $ Two () b a, Just $ Five () g f e d c)
shiftL (Four () d c b a) (Four () h g f e) = (Just $ Three () c b a, Just $ Five () h g f e d)
shiftL (Five () e d c b a) (One () f) = (Just $ One () a, Just $ Five () f e d c b)
shiftL (Five () e d c b a) (Two () g f) = (Just $ Two () b a, Just $ Five () g f e d c)
shiftL (Five () e d c b a) (Three () h g f) = (Just $ Three () c b a, Just $ Five () h g f e d)
shiftL (Five () e d c b a) (Four () i h g f) = (Just $ Four () d c b a, Just $ Five () i h g f e)

overfill :: Unit -> a -> Block a () -> (Block a (), Block a ())
overfill u x (Five () e d c b a) = (Three () b a x, Three () e d c)

isFull :: Block a () -> Bool
isFull (Five () _ _ _ _ _) = True
isFull _ = False

-- | Pushing works as follows:
--   - If a block has less than k elements, it is safe.
--   - If a block has k elements, it is dangerous.
--     We need to push out the other block in the digit.
--   - If a block is full, we create a new node
-- This type should be unboxed.
data PushState o a p = Safe (Block a p) Unit | Dangerous (Block a ()) p Unit | Full (Digit o a)
  deriving (Eq, Ord, Show)

pushBlock :: a -> Block a p -> Unit -> PushState o a p
pushBlock x (One p a) u = Safe (Two p a x) u
pushBlock x (Two p b a) u = Safe (Three p b a x) u
pushBlock x (Three p c b a) u = Safe (Four p c b a x) u
pushBlock x (Four p d c b a) u = Dangerous (Five () d c b a x) p u
pushBlock x (Five _ e d c b a) _ = Full (Digit (One (Just (Five () e d c b a)) x))

-- This type should be unboxed.
data PopState a p = NowEmpty a p Unit | Occupied a (Block a p)
  deriving (Eq, Ord, Show)

popBlock :: Block a p -> PopState a p
popBlock (One p a) = NowEmpty a p Unit
popBlock (Two p b a) = Occupied a (One p b)
popBlock (Three p c b a) = Occupied a (Two p c b)
popBlock (Four p d c b a) = Occupied a (Three p d c b)
popBlock (Five p e d c b a) = Occupied a (Four p e d c b)

-- This part is independent of the block size k

-- FIPness constraints:
-- - singleton may use one space credit
-- - pop needs to return a space credit with empty digit
-- - nodeToDigit may not use space credits
-- - toTree may use one space credit
-- - to make glue fip, we may never have fully filled digits

-- | Contains 1..k elements
newtype Node v a = Node (Block a v)
  deriving (Eq, Ord, Show)

instance Measured a v => Measured (Node v a) v where
  measure (Node b) = snd $ breakBlock b

blockToDigit :: Block a () -> Digit o a
blockToDigit b = Digit (addBlock Nothing b)

nodeToBlock :: Node v a -> Block a ()
nodeToBlock (Node b) = fst $ breakBlock b

blockToNode :: Measured a v => Block a () -> Node v a
blockToNode (One () a) = undefined
blockToNode b = Node (addBlock (measure b) b)

singleton :: Unit -> a -> Digit o a
singleton _ a = Digit (One Nothing a)

doubleton :: Unit -> a -> a -> Digit o a
doubleton _ a b = Digit (Two Nothing b a)

-- | Push takes a space credit and may return a node
push :: a -> Digit o a -> Unit -> (Digit o a, Maybe (Block a (), Unit))
push x d u = case pushBlock x (unDigit d) u of
  Safe d _ -> (Digit d, Nothing)
  Dangerous d Nothing u -> (blockToDigit d, Nothing)
  Dangerous d (Just b) u -> (blockToDigit d, Just (b, u))
  Full d -> (d, Nothing)

headDigit :: Digit o a -> a
headDigit d = case popBlock (unDigit d) of
  NowEmpty x _ _ -> x
  Occupied x _ -> x

-- | Pop takes an element from the block.
-- If the resulting digit is empty, it will return a space credit.
pop :: Digit o a -> (a, Either Unit (Digit o a))
pop d = case popBlock (unDigit d) of
    Occupied x d -> (x, Right $ Digit d)
    NowEmpty x Nothing u -> (x, Left u) -- return space credit
    NowEmpty x (Just back) u -> (x, Right (blockToDigit back)) -- could return space credit

digitToList :: Digit 'Ordered a -> [a]
digitToList d =
  let (b, m) = breakBlock (unDigit d) in
  blockToList b ++ maybe [] blockToList m

nodeToDigit :: Node v a -> Digit 'Ordered a
nodeToDigit = blockToDigit . nodeToBlock

nodeToList :: Node v a -> [a]
nodeToList = blockToList . nodeToBlock

-- | Pad all to four elements
data FIP v a m
  = Empty
  | Single a
  | SDigit (Digit 'Ordered a)
  | Deep v (Digit 'Ordered a) (Thunk m (FLazyCon m) (FIP v (Node v a) m)) (Digit 'Flipped a)

data FLazyCon m a where
  FCons :: Measured a v => a -> Thunk m (FLazyCon m) (FIP v a m) -> FLazyCon m (FIP v a m)
  FSnoc :: Measured a v => Thunk m (FLazyCon m) (FIP v a m) -> a -> FLazyCon m (FIP v a m)
  FDeepL :: Measured a v => v -> () -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Digit 'Flipped a -> FLazyCon m (FIP v a m)
  FDeepR :: Measured a v => v -> Digit 'Ordered a -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> () -> FLazyCon m (FIP v a m)

instance MonadCredit m => HasStep (FLazyCon m) m where
  -- We get a space credit from the thunk
  step (FCons x m) = cons Unit x =<< force m
  step (FSnoc m x) = flip (snoc Unit) x =<< force m
  step (FDeepL v () m sf) = deepL Unit Nothing v m sf
  step (FDeepR v pr m ()) = deepR Unit pr v m Nothing

instance Measured a v => Measured (FIP v a m) v where
  measure Empty = mempty
  measure (Single x) = measure x
  measure (SDigit d) = measure d
  measure (Deep vm f m r) = measure f <> vm <> measure (flipDigit r)

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

  concat q1 q2 = glue q1 Nothing q2
  splitTree = splitTree
  treeToList q = treeToListAcc [] (\x -> [x]) q

-- Amortization idea:
--  - FCons and FSnoc both cost two credits
--  - FDeepL and FDeepR both cost three credits
--  - the first credit is used to tick
--  - We maintain the invariant:
--    - The m thunk requires two or three credits to force,
--    - In each queue Deep(f, m, r), m has dang(f) + isDeepLR(m) + dang(r) credits,
--      where dang(d) = if isSafe(d) then 0 else 1.
--      and isDeepLR(m) = 1 if m is a FDeepL or FDeepR thunk, 0 otherwise.
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

deep :: (MonadCredit m, Measured a v) => v -> Digit 'Ordered a -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Digit 'Flipped a -> Unit -> m (FIP v a m)
deep v f m r _ = do
  let dang d = if isSafe d then 0 else 1
  isDeepLR <- lazymatch m (\_ -> pure 0) (\case
    FDeepL {} -> pure 1
    FDeepR {} -> pure 1
    _ -> pure 0)
  m `hasAtLeast` (dang f + isDeepLR + dang r)
  lazymatch m (\m -> when (v /= measure m) $ fail "invalid measure") (\_ -> pure ())
  pure $ Deep v f m r

deep' :: (MonadCredit m, Measured a v) => v -> Digit 'Ordered a -> m (Thunk m (FLazyCon m) (FIP v (Node v a) m)) -> Digit 'Flipped a -> Unit -> m (FIP v a m)
deep' vm f mkM r u = do
  m <- mkM
  deep vm f m r u

cons :: (MonadCredit m, Measured a v) => Unit -> a -> FIP v a m -> m (FIP v a m)
cons u1 a q = do
  tick
  case q of
    Empty -> pure $ Single a
    Single b -> pure $ SDigit (doubleton u1 a b) -- at Single
    SDigit d -> deep' mempty (singleton u1 a) vempty (flipDigit d) Unit -- at SDigit
    Deep vm pr m sf ->
      case push a pr Unit of -- Unit from Deep
        (pr', Nothing) -> do
          m `creditWith` 1
          deep vm pr' m sf u1
        (pr', Just (b, u)) -> do
          unless (isFull b) $ fail "cons: block should be full"
          let node = blockToNode b
          m' <- delay $ FCons node m -- at u
          if isSafe sf
            then m  `creditWith` 1
            else m' `creditWith` 1
          deep (measure node <> vm) pr' m' sf u1

head :: MonadCredit m => FIP v a m -> m a
head Empty = fail "head: empty queue"
head (Single x) = pure x
head (SDigit d) = pure $ headDigit d
head (Deep _ pr _ _) = pure $ headDigit pr

uncons :: (MonadCredit m, Measured a v) => FIP v a m -> m (Maybe (a, Thunk m (FLazyCon m) (FIP v a m)))
uncons q = do
  tick
  case q of
    Empty -> pure $ Nothing
    Single a -> do
      e <- vempty
      pure $ Just (a, e)
    SDigit d -> case pop d of
      (a, Left u) -> do
        t <- vempty
        pure $ Just (a, t)
      (a, Right d') -> do
        t <- value $ SDigit d'
        pure $ Just (a, t)
    Deep vm pr m sf -> do
      case pop pr of
        (a, Left u) -> do
          t <- delay $ FDeepL vm () m sf -- at Deep
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

deepL :: (MonadCredit m, Measured a v) => Unit -> Maybe (Digit 'Ordered a) -> v -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Digit 'Flipped a -> m (FIP v a m)
deepL u1 Nothing _ m sf = do
  when (isSafe sf) $ m `creditWith` 1
  m' <- force m
  let mt = measureTail m'
  m'' <- uncons m'
  case m'' of
    Nothing -> pure $ SDigit (flipDigit sf)
    Just (h, t) -> do -- h is safe
      unless (isSafe sf) $ t `creditWith` 1
      let pr = nodeToDigit h
      unless (isSafe pr) $ fail "deepL: new pr has to be safe"
      deep mt pr t sf u1
deepL u1 (Just pr) vm m sf = deep vm pr m sf u1

-- | FIP if it takes its argument as borrowed and returns int
measureTail :: Measured a v
            => FIP v (Node v a) m -> v
measureTail q = case q of
  Empty -> mempty
  Single _ -> mempty
  SDigit d -> (case pop d of
    (_, Left u) -> mempty
    (_, Right d') -> measure d') 
  Deep v pr _ sf -> (case pop pr of
    (_, Left u) -> mempty
    (_, Right pr') -> measure pr') <> v <> measure (flipDigit sf)

snoc :: (MonadCredit m, Measured a v)
     => Unit -> FIP v a m -> a -> m (FIP v a m)
snoc u1 q e = do
  tick
  case q of
    Empty -> pure $ Single e -- at u1
    Single a -> pure $ SDigit (doubleton u1 a e) -- at Single
    SDigit d -> deep' mempty d vempty (singleton u1 e) Unit -- at SDigit
    Deep vm pr m sf ->
      case push e sf Unit of -- from Deep
        (sf', Nothing) -> do
          m `creditWith` 1
          deep vm pr m sf' u1
        (sf', Just (b, u)) -> do
          unless (isFull b) $ fail "snoc: block should be full"
          let node = blockToNode (flipBlock b)
          t <- delay $ FSnoc m node -- at u
          if isSafe pr
            then m `creditWith` 1
            else t `creditWith` 1
          deep (vm <> measure node) pr t sf' u1

last :: (MonadCredit m, Measured a v) => FIP v a m -> m a
last Empty = fail "last: empty queue"
last (Single x) = pure x
last (SDigit d) = pure $ headDigit $ flipDigit d
last (Deep _ _ _ sf) = pure $ headDigit sf

unsnoc :: (MonadCredit m, Measured a v) => FIP v a m -> m (Maybe (Thunk m (FLazyCon m) (FIP v a m), a))
unsnoc q = do
  tick
  case q of
    Empty -> pure $ Nothing
    Single a -> do
      e <- vempty
      pure $ Just (e, a)
    SDigit d -> case pop (flipDigit d) of
      (a, Left u) -> do
        t <- vempty
        pure $ Just (t, a)
      (a, Right d') -> do
        t <- value $ SDigit (flipDigit d')
        pure $ Just (t, a)
    Deep vm pr m sf ->
      case pop sf of
        (a, Left u) -> do
          t <- delay $ FDeepR vm pr m () -- from Deep
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

deepR :: (MonadCredit m, Measured a v) => Unit -> Digit 'Ordered a -> v -> Thunk m (FLazyCon m) (FIP v (Node v a) m) -> Maybe (Digit 'Flipped a) -> m (FIP v a m)
deepR u1 pr _ m Nothing = do
  when (isSafe pr) $ m `creditWith` 1
  m' <- force m
  let mi = measureInit m'
  m'' <- unsnoc m'
  case m'' of
    Nothing -> pure $ SDigit pr
    Just (t, l) -> do -- l is safe
      unless (isSafe pr) $ t `creditWith` 1
      let sf = flipDigit $ nodeToDigit l
      unless (isSafe sf) $ fail "deepR: new sf has to be safe"
      deep mi pr t sf u1
deepR u1 s vm m (Just sf) = deep vm s m sf u1

measureInit :: Measured a v
            => FIP v (Node v a) m -> v
measureInit q = case q of
  Empty -> mempty
  Single _ -> mempty
  SDigit d -> (case pop (flipDigit d) of
    (_, Left u) -> mempty
    (_, Right d') -> measure (flipDigit d'))
  Deep v pr _ sf -> measure pr <> v <> (case pop sf of
    (_, Left u) -> mempty
    (_, Right sf') -> measure (flipDigit sf'))

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

foldDigit :: Monad m => (b -> a -> m b) -> b -> Digit o a -> m b
foldDigit f acc d = case pop d of
  (a, Left _) -> f acc a
  (a, Right d') -> do
    acc' <- f acc a
    foldDigit f acc' d'

foldMBlock :: Monad m => (b -> a -> m b) -> b -> Maybe (Block a ()) -> m b
foldMBlock f acc Nothing = pure acc
foldMBlock f acc (Just b) = foldDigit f acc (blockToDigit b)

-- | Push an element into the block and assert that no overflow occurs.
-- This does not have to allocate.
unsafePush :: a -> Block a () -> Block a ()
unsafePush n b = case pushBlock n b Unit of
  Safe b Unit -> b
  Dangerous b () Unit -> b

pushShifted :: Measured a v => Maybe (Block a ()) -> (Maybe (Block a ()), Either Unit (Block (Node v a) ())) -> (Maybe (Block a ()), Either Unit (Block (Node v a) ()))
pushShifted Nothing (Nothing, e) = (Nothing, e)
pushShifted Nothing ((Just b), e) = (Just b, e)
pushShifted (Just b) (Nothing, e) = (Just b, e)
pushShifted (Just b) ((Just b'), e) =
  let (pf, ff) = shiftL b b' in
  (pf, case ff of
    Nothing -> e
    Just ff -> case e of
      -- Create a singleton block:
      Left Unit -> Right (One () (blockToNode ff))
      -- Push into the existing block:
      -- (this succeeds as we have at most 5 elements)
      Right b -> Right $ unsafePush (blockToNode ff) b)

pushLast :: Measured a v => (Maybe (Block a ()), Either Unit (Block (Node v a) ())) -> Block (Node v a) ()
pushLast (Nothing, Right b) = b
pushLast (Just (One () a), Left _) = undefined
pushLast (Just b, Left _) = One () (blockToNode b)
pushLast (Just (One () a), Right b') = case popBlock b' of
  NowEmpty n () Unit ->
    let (a', n') = overfill Unit a (nodeToBlock n) in -- from One
    Two () (blockToNode n') (blockToNode a') -- from NowEmpty
  Occupied n b'' ->
    let (a', n') = overfill Unit a (nodeToBlock n) in -- from One
    unsafePush (blockToNode a') $ unsafePush (blockToNode n') b''
pushLast (Just b, Right b') = unsafePush (blockToNode b) b'

-- | Needs k + five allocations in the base case to cons/snoc.
glue :: (MonadCredit m, Measured a v) => FIP v a m -> Maybe (Block a ()) -> FIP v a m -> m (FIP v a m)
glue Empty as q2 = foldMBlock (\q a -> cons Unit a q) q2 (fmap flipBlock as)
glue q1 as Empty = foldMBlock (snoc Unit) q1 as
glue (Single x) as q2 = do 
  q3 <- foldMBlock (\q a -> cons Unit a q) q2 (fmap flipBlock as)
  cons Unit x q3 -- from Single
glue q1 as (Single y) = do
  q3 <- foldMBlock (snoc Unit) q1 as
  snoc Unit q3 y -- from Single
glue (SDigit d1) as q2 = do
  q3 <- foldMBlock (\q a -> cons Unit a q) q2 (fmap flipBlock as)
  foldDigit (\q a -> cons Unit a q) q3 (flipDigit d1)
glue q1 as (SDigit d2) = do
  q3 <- foldMBlock (snoc Unit) q1 as
  foldDigit (snoc Unit) q3 d2
glue (Deep _ u1 q1 v1) as (Deep _ u2 q2 v2) = tick >> do
  creditWith q1 2
  q1 <- force q1
  creditWith q2 2
  q2 <- force q2
  let (a, b) = breakBlock $ unDigit (flipDigit v1)
  let (d, e) = breakBlock $ unDigit u2
  let as' = pushLast $
              pushShifted (Just a) $
              pushShifted b $
              pushShifted as $
              pushShifted (Just d) $
              pushShifted e $
              (Nothing, Left Unit) -- from first Deep
  q <- glue q1 (Just as') q2
  deep' (measure q) u1 (value q) v2 Unit -- from second Deep

-- | Split one digit into two: requires up to one allocation.
splitDigit :: Measured a v => (v -> Bool) -> v -> Digit 'Ordered a -> (Maybe (Digit 'Ordered a), a, Maybe (Digit 'Ordered a))
splitDigit p i d =
  let (b, m) = breakBlock (unDigit d) in
  case (m, p (i <> measure b)) of
    (Just m, False) ->
      let (l, x, r) = splitBlock p (i <> measure b) m in
      (Just (mkDigit b l), x, fmap blockToDigit r)
    (m, _) ->
      let (l, x, r) = splitBlock p i b in
      (fmap blockToDigit l, x, case r of
        Nothing -> fmap blockToDigit m
        Just r -> Just $ mkDigit r m)

mtoTree :: (MonadCredit m, Measured a v) => Unit -> Maybe (Digit 'Ordered a) -> m (FIP v a m)
mtoTree u m = pure $ maybe Empty SDigit m

-- | Requires two allocations per recursive call: to split the digit and to create the new Deep node.
splitTree :: (MonadCredit m, Measured a v) => (v -> Bool) -> v -> FIP v a m -> m (Split FIP v a m)
splitTree p i Empty = fail "splitTree: empty tree"
splitTree p i (Single x) = pure $ Split Empty x Empty -- from Single
splitTree p i (SDigit d) = do
  let (l, x, r) = splitDigit p i d
  Split <$> mtoTree Unit l <*> pure x <*> mtoTree Unit r
splitTree p i (Deep vm pr m sf) = do
  tick
  m `creditWith` 2
  let vpr = i <> measure pr
  let vprm = vpr <> vm
  if p vpr then do
    let (l, x, r) = splitDigit p i pr
    ml <- vempty
    Split <$> mtoTree Unit l <*> pure x <*> deepL Unit r vm m sf
  else if p vprm then do
    Split ml xs mr <- splitTree p vpr =<< force m
    [ml', mr'] <- mapM value [ml, mr]
    let (vml, vmr) = (measure ml, measure mr)
    let (l, x, r) = splitDigit p (vpr <> vml) (nodeToDigit xs)
    Split <$> deepR Unit pr vml ml' (fmap flipDigit l) <*> pure x <*> deepL Unit r vmr mr' sf
  else do
    let (l, x, r) = splitDigit p vprm (flipDigit sf)
    mr <- vempty
    Split <$> deepR Unit pr vm m (fmap flipDigit l) <*> pure x <*> mtoTree Unit r

append :: MonadCredit m => [a] -> [a] -> m [a]
append [] ys = pure ys
append (x : xs) ys = tick >> fmap (x:) (append xs ys)

treeToListAcc :: MonadCredit m => [b] -> (a -> [b]) -> FIP v a m -> m [b]
treeToListAcc acc f Empty = pure acc
treeToListAcc acc f (Single x) = append (f x) acc
treeToListAcc acc f (SDigit d) = append (concatMap f (digitToList d)) acc
treeToListAcc acc f (Deep _ pr m sf) = do
  let pr' = concatMap f $ digitToList pr
  let sf' = concatMap f $ digitToList $ flipDigit sf
  acc' <- append sf' acc
  creditWith m 2
  m' <- treeToListAcc acc' (concatMap f . nodeToList) =<< force m
  append pr' m'

instance (MemoryCell m a, MemoryCell m p) => MemoryCell m (Block a p) where
  prettyCell (One p a) = do
    a' <- prettyCell a
    p' <- prettyCell p
    pure $ mkMCell "One" [p', a']
  prettyCell (Two p b a) = do
    a' <- prettyCell a
    b' <- prettyCell b
    p' <- prettyCell p
    pure $ mkMCell "Two" [p', a', b']
  prettyCell (Three p c b a) = do
    a' <- prettyCell a
    b' <- prettyCell b
    c' <- prettyCell c
    p' <- prettyCell p
    pure $ mkMCell "Three" [p', a', b', c']
  prettyCell (Four p d c b a) = do
    a' <- prettyCell a
    b' <- prettyCell b
    c' <- prettyCell c
    d' <- prettyCell d
    p' <- prettyCell p
    pure $ mkMCell "Four" [p', a', b', c', d']
  prettyCell (Five p e d c b a) = do
    a' <- prettyCell a
    b' <- prettyCell b
    c' <- prettyCell c
    d' <- prettyCell d
    e' <- prettyCell e
    p' <- prettyCell p
    pure $ mkMCell "Five" [p', a', b', c', d', e']

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Digit 'Ordered a) where
  prettyCell = prettyCell . unDigit

instance (MonadMemory m, MemoryCell m a) => MemoryCell m (Node v a) where
  prettyCell = prettyCell . nodeToBlock

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

instance (MonadMemory m, MemoryCell m a, MemoryCell m v) => MemoryCell m (FIP v a m) where
  prettyCell Empty = pure $ mkMCell "Empty" []
  prettyCell (Single a) = do
    a' <- prettyCell a
    pure $ mkMCell "Single" [a']
  prettyCell (SDigit d) = do
    d' <- prettyCell d
    pure $ mkMCell "SDigit" [d']
  prettyCell (Deep v s q u) = do
    v' <- prettyCell v
    s' <- prettyCell s
    q' <- prettyCell q
    u' <- prettyCell (flipDigit u)
    pure $ mkMCell "Deep" [v', s', q', u']

instance (forall m. Monad m => MemoryCell m a, forall m. Monad m => MemoryCell m v) => MemoryStructure (FIP v a) where
  prettyStructure = prettyCell