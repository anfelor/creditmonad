{-# LANGUAGE DerivingStrategies, FunctionalDependencies, AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}

module Test.Credit
  (
  -- * Common Time-Complexity Functions
    Size, logstar, log2, linear
  -- * Execution Traces for Testing
  , Strategy(..), genExecutionTrace
  -- * Running Data Structures on Execution Traces
  , DataStructure(..), runTree, runTreeTrace
  -- * Testing Data Structures on Execution Traces
  , checkCredits, checkCreditsTrace
  ) where

import Data.Either
import Control.Monad.State
import Data.Tree
import Test.QuickCheck
import Prettyprinter
import Prettyprinter.Render.String

import Control.Monad.Credit.Base
import Control.Monad.Credit.CreditM

path :: Arbitrary a => Int -> Tree a -> Gen (Tree a)
path 0 end = pure end
path n end = Node <$> arbitrary <*> ((:[]) <$> path (n-1) end)

path' :: Arbitrary a => Int -> Gen (Tree a)
path' n = path n =<< Node <$> arbitrary <*> pure []

bloom :: Arbitrary a => Gen (Tree a)
bloom = sized $ \n -> do
  m <- chooseInt (0, n)
  k <- chooseInt (0, m `div` 2)
  ts <- mapM (\_ -> path' (m `div` k)) [1..k]
  path (n - m) =<< Node <$> arbitrary <*> pure ts

pennant :: Arbitrary a => Gen (Tree a)
pennant = sized go
  where
    go n | n <= 1 = path' 0
    go n = do
      k <- chooseInt (n `div` 3, 2 * (n `div` 3))
      ts <- mapM (\_ -> go ((n - k - 1) `div` 2)) [1..2]
      path k =<< Node <$> arbitrary <*> pure ts

newtype SeqTree a = SeqTree { fromSeqTree :: Tree a }
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (SeqTree a) where
  arbitrary = sized $ \n -> SeqTree <$> path' n

newtype BloomTree a = BloomTree { fromBloomTree :: Tree a }
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (BloomTree a) where
  arbitrary = BloomTree <$> bloom

newtype PennantTree a = PennantTree { fromPennantTree :: Tree a }
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (PennantTree a) where
  arbitrary = PennantTree <$> pennant

newtype PrsTree a = PrsTree { fromPrsTree :: Tree a }
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (PrsTree a) where
  arbitrary = PrsTree <$> arbitrary

data Strategy = Path | Bloom | Pennant | Random
  deriving (Eq, Ord, Show)

genExecutionTrace :: Arbitrary op => Strategy -> Gen (Tree op)
genExecutionTrace Path = fromSeqTree <$> arbitrary
genExecutionTrace Bloom = fromBloomTree <$> arbitrary
genExecutionTrace Pennant = fromPennantTree <$> arbitrary
genExecutionTrace Random = fromPrsTree <$> arbitrary

newtype Size = Size Int
  deriving (Eq, Ord, Show)
  deriving newtype (Num, Enum, Real, Integral, Pretty)

instance Monad m => MemoryCell m Size where
  prettyCell (Size i) = pure $ mkMCell (show i) []

logstar :: Size -> Credit
logstar (Size n) = fromInteger $ go n 0
  where
    go n acc | n < 2 = acc
    go n acc = go (log2 n 0) (acc + 1)

    log2 n acc | n < 2 = acc
    log2 n acc = log2 (n `div` 2) (acc + 1)

log2 :: Size -> Credit
log2 (Size n) = fromInteger $ go n 0
  where
    go n acc | n < 2 = acc
    go n acc = go (n `div` 2) (acc + 1)

linear :: Size -> Credit
linear (Size n) = fromInteger $ toInteger n

class (Arbitrary op, Show op) => DataStructure t op | t -> op where
  cost :: Size -> op -> Credit
  -- ^ Given a size and an operation, return the cost of the operation.
  -- This function can not inspect the internal state of the data structure.
  create :: MonadLazy m => m (t m)
  -- ^ create a new instance of the data structure.
  -- We allow the computation to be lazy, since lazy data structures
  -- often contain thunks even if they contain no elements.
  -- The create data structure is assumed to have size zero.
  perform :: MonadInherit m => Size -> t m -> op -> m (Size, t m)
  -- ^ Given a data structure, its size, and an operation,
  -- return the updated size and data structure.
  -- We allow the size to depend on the internal state of the data structure,
  -- since some operations, like insertions into a binary search tree, might
  -- return different sizes depending on whether a new element is already present.

-- | Evaluate an execution trace of operations on the given data structure
-- using the credit monad. Returns either an error or unit if the evaluation succeeded.
runTree :: forall t op. DataStructure t op => Tree op -> Either Error ()
runTree tree = runCreditM 0 (create @t >>= flip (go 0) tree)
  where
    go :: forall s t op. DataStructure t op => Size -> t (CreditM s) -> Tree op -> CreditM s ()
    go sz a (Node op ts) = do
      let cr = cost @t sz op
      resetCurrentThunk cr
      (sz, a) <- perform sz a op
      mapM_ (go sz a) ts

isPersistent :: Tree a -> Bool
isPersistent (Node _ ts) = length ts > 1 || any isPersistent ts

-- | Test the given data structure in the credit monad using the given strategy.
-- This property only reports if evaluation succeeded or not.
checkCredits :: forall t op. DataStructure t op => Strategy -> Property
checkCredits strat =
  forAllShrink (genExecutionTrace strat) shrink $ \t ->
    classify (isPersistent t) "persistent" $
      isRight $ runTree @t t

data RoseZipper a = Root | Branch a [Tree a] (RoseZipper a)
  deriving (Eq, Ord, Show)

up :: RoseZipper a -> RoseZipper a
up (Branch x ls (Branch y rs z)) = Branch y (Node x (reverse ls) : rs) z
up z = z

extend :: String -> RoseZipper String -> RoseZipper String
extend s (Branch x ls z) = Branch (x ++ s) ls z
extend _ Root = Root

extract :: RoseZipper a -> Tree a
extract (Branch x ls Root) = Node x (reverse ls)
extract z = extract (up z)

-- | If each node has only a single child, flatten the tree
-- by making all elements children of the root.
-- This improves the readability of the tree when printed.
-- Otherwise, return the original tree.
flattenTree :: Tree a -> Tree a
flattenTree t = case go t of
  Just (x:xs) -> Node x (map (\x -> Node x []) xs)
  _ -> t
  where
    go (Node x []) = Just [x]
    go (Node x [t]) = (x :) <$> go t
    go (Node _ _) = Nothing

showState :: (Either Error (), RoseZipper String) -> String
showState (Left e, t) = drawTree $ flattenTree $ extract $ extend (show $ pretty e) t
showState (Right (), t) = drawTree $ flattenTree $ extract t

type M s = CreditT s (State (RoseZipper String))

-- | Evaluate an execution trace of operations on the given data structure
-- using the credit monad. Returns a pretty-printed string of the execution trace
-- annotated with the internal state of the data structure at each step.
runTreeTrace :: forall t op. (MemoryStructure t, DataStructure t op) => Tree op -> String
runTreeTrace tree = showState $ runState (runCreditT 0 (create @t >>= flip (go 0) tree)) Root
  where
    go :: forall s t op. (MemoryStructure t, DataStructure t op) => Size -> t (M s) -> Tree op -> M s ()
    go sz a (Node op ts) = do
      let cr = cost @t sz op
      resetCurrentThunk cr
      lift $ modify' (Branch (show op ++ ": ") []) 
      (sz, a) <- perform sz a op
      mem <- prettyStructure a
      let s = renderString $ layoutSmart (defaultLayoutOptions { layoutPageWidth = Unbounded }) $ nest 2 $ pretty $ mem
      lift $ modify' (extend s)
      mapM_ (go sz a) ts
      lift $ modify' up

-- | Test the given data structure in the credit monad using the given strategy.
-- If evaluation fails, this property prints the execution trace
-- annotated with the internal state of the data structure at each step.
checkCreditsTrace :: forall t op. (MemoryStructure t, DataStructure t op) => Strategy -> Property
checkCreditsTrace strat =
  forAllShrinkShow (genExecutionTrace strat) shrink (\t -> runTreeTrace @t t) $ \t ->
    classify (isPersistent t) "persistent" $
      isRight $ runTree @t t