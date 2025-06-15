{-# LANGUAGE DerivingStrategies, FunctionalDependencies, AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}

module Test.Credit
  (
  -- * Common time-complexity functions
    Size, logstar, log2, linear
  -- * Tree shapes for testing
  , Strategy(..), genTree
  -- * Testing data structures on trees of operations
  , DataStructure(..), runTree, checkCredits, runTreeMemory, checkCreditsMemory
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

genTree :: Arbitrary op => Strategy -> Gen (Tree op)
genTree Path = fromSeqTree <$> arbitrary
genTree Bloom = fromBloomTree <$> arbitrary
genTree Pennant = fromPennantTree <$> arbitrary
genTree Random = fromPrsTree <$> arbitrary

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
  create :: forall m. MonadInherit m => t m
  action :: forall m. MonadInherit m => t m -> op -> (Credit, m (t m))

runTree :: forall t op. DataStructure t op => Tree op -> Either Error ()
runTree tree = runCreditM 0 (go (create @t) tree)
  where
    go :: forall s t op. DataStructure t op => t (CreditM s) -> Tree op -> CreditM s ()
    go a (Node op ts) = do
      let (cr, f) = action a op
      resetCurrentThunk cr
      a' <- f
      mapM_ (go a') ts

isPersistent :: Tree a -> Bool
isPersistent (Node _ ts) = length ts > 1 || any isPersistent ts

-- | Evaluate the queue operations using the given strategy on the given queue
-- Reports only if evaluation succeeded.
checkCredits :: forall t op. DataStructure t op => Strategy -> Property
checkCredits strat =
  forAllShrink (genTree strat) shrink $ \t ->
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

runTreeMemory :: forall t op. (MemoryStructure t, DataStructure t op) => Tree op -> String
runTreeMemory tree = showState $ runState (runCreditT 0 (go (create @t) tree)) Root
  where
    go :: forall s t op. (MemoryStructure t, DataStructure t op) => t (M s) -> Tree op -> M s ()
    go a (Node op ts) = do
      let (cr, f) = action a op
      resetCurrentThunk cr
      lift $ modify' (Branch (show op ++ ": ") []) 
      a' <- f
      mem <- prettyStructure a'
      let s = renderString $ layoutSmart (defaultLayoutOptions { layoutPageWidth = Unbounded }) $ nest 2 $ pretty $ mem
      lift $ modify' (extend s)
      mapM_ (go a') ts
      lift $ modify' up

-- | Evaluate the queue operations using the given strategy on the given queue
-- Reports only if evaluation succeeded.
checkCreditsMemory :: forall t op. (MemoryStructure t, DataStructure t op) => Strategy -> Property
checkCreditsMemory strat =
  forAllShrinkShow (genTree strat) shrink (\t -> runTreeMemory @t t) $ \t ->
    classify (isPersistent t) "persistent" $
      isRight $ runTree @t t