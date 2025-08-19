{-# LANGUAGE AllowAmbiguousTypes, TypeApplications #-}

-- | Testing the code in the introduction of the paper.
module Intro where

import Control.Monad
import Control.Monad.Credit
import Test.Credit
import Test.QuickCheck
import Data.Tree

data Batched a m = Batched [a] [a]
  deriving (Eq, Ord, Show)

rev :: MonadCount m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc)

batched :: MonadCount m => [a] -> [a] -> m (Batched a m)
batched [] rear = do
  front <- rev rear []
  pure $ Batched front []
batched front rear = pure $ Batched front rear

empty :: MonadCount m => m (Batched a m)
empty = pure $ Batched [] []

snoc :: MonadCount m => Batched a m -> a -> m (Batched a m)
snoc   (Batched front rear) x = batched front (x : rear)

uncons :: MonadCount m => Batched a m -> m (Maybe (a, Batched a m))
uncons (Batched [] []) = pure Nothing
uncons (Batched (x:front) rear) = do
  q' <- batched front rear
  pure $ Just (x, q')

unfoldM :: Monad m => (b -> m (Maybe (a, b))) -> b -> m [a] 
unfoldM f b = do
  mb <- f b
  case mb of
    Nothing -> pure []
    Just (x, b') -> (x :) <$> unfoldM f b'

testBatched :: Either String ([Int], Ticks)
testBatched =
  runCounterM $ empty >>= flip (foldM snoc) [1..10]
                      >>= unfoldM uncons

data QueueOp a = Snoc a | Uncons
  deriving (Eq, Ord, Show)

instance Arbitrary a => Arbitrary (QueueOp a) where
  arbitrary = frequency
    [ (7, Snoc <$> arbitrary), (3, pure Uncons) ]

instance (Arbitrary a, Show a)
      => DataStructure (Batched a) (QueueOp a) where
  create = pure $ Batched [] []

  perform sz q (Snoc x) = (sz + 1,) <$> snoc q x
  perform sz q Uncons = do
    m <- uncons q
    case m of
      Nothing -> pure (sz, Batched [] [])
      Just (_, q') -> pure (sz - 1, q')

  cost n (Snoc _) = 1
  cost n Uncons   = 0

testSeq :: IO ()
testSeq = quickCheck $ checkCredits @(Batched Int) Path

genTree :: Strategy -> IO ()
genTree s = 
  putStrLn . drawTree . fmap show
    =<< generate (genExecutionTrace @(QueueOp Int) s)

testPar :: IO ()
testPar = quickCheck $ checkCredits @(Batched Int) Random