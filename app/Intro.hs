{-# LANGUAGE AllowAmbiguousTypes, TypeApplications #-}

-- | Testing the code in the introduction of the paper.
module Intro where

import Control.Monad
import System.Environment (getArgs)
import Test.QuickCheck

import Control.Monad.Credit

data Batched a = Batched [a] [a]
  deriving (Eq, Ord, Show)

rev :: MonadCount m => [a] -> [a] -> m [a]
rev [] acc = pure acc
rev (x : xs) acc = tick >> rev xs (x : acc)

batched :: MonadCount m => [a] -> [a] -> m (Batched a)
batched [] rear = do
  front <- rev rear []
  pure $ Batched front []
batched front rear = pure $ Batched front rear

empty :: MonadCount m => m (Batched a)
empty = pure $ Batched [] []

snoc :: MonadCount m => Batched a -> a -> m (Batched a)
snoc   (Batched front rear) x = batched front (x : rear)

uncons :: MonadCount m => Batched a -> m (Maybe (a, Batched a))
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