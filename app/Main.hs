{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, DerivingStrategies #-}

module Main where

import UnliftIO.Internals.Async
import System.Environment (getArgs)
import Test.QuickCheck
import Prettyprinter

import Control.Monad.Credit
import Test.Credit
import Test.Credit.Queue.Base
import Test.Credit.Queue.Batched
import Test.Credit.Queue.Bankers
import Test.Credit.Queue.Physicists
import Test.Credit.Queue.Realtime
import Test.Credit.Queue.Bootstrapped
import Test.Credit.Queue.Implicit
import Test.Credit.Deque.Base
import Test.Credit.Deque.Bankers
import Test.Credit.Deque.Realtime
import Test.Credit.Deque.Catenable
import Test.Credit.Deque.SimpleCat
import Test.Credit.Deque.ImplicitCat
import Test.Credit.Finger
import Test.Credit.Heap.Base
import Test.Credit.Heap.Binomial
import Test.Credit.Heap.ZBinomial
import Test.Credit.Heap.LazyPairing
import Test.Credit.Heap.LazyPairingFIP
import Test.Credit.Heap.Pairing
import Test.Credit.Heap.Scheduled
import Test.Credit.Heap.Maxiphobic
import Test.Credit.Heap.RoundRobin
import Test.Credit.Sortable.Base
import Test.Credit.Sortable.MergeSort
import Test.Credit.Sortable.Scheduled
import Test.Credit.RandomAccess.Base
import Test.Credit.RandomAccess.Binary
import Test.Credit.RandomAccess.Zeroless

import Talk

run :: forall t op. (MemoryStructure t, DataStructure t op) => Args -> Strategy -> IO Result
run args strat = quickCheckWithResult args $ checkCreditsTrace @t strat

newtype Alpha = Alpha Char
  deriving (Eq, Ord)
  deriving newtype (Pretty)

instance Show Alpha where
  show (Alpha c) = [c]

instance Arbitrary Alpha where
  arbitrary = Alpha <$> frequency
    [ (1, choose ('a', 'z')), (1, choose ('A', 'Z')) ]

benchmarks :: Args -> [(String, IO Result)]
benchmarks args =
  [ (benchs ++ ":", runB args Path)
  | (benchs, runB) <- reverse
      [ ("Batched Queue", run @(Q Batched Alpha))
      , ("Pairing Heap", run @(H Pairing Alpha))
      , ("Pairing Heap (Merge)", run @(BH Pairing Alpha))
      , ("RoundRobin Heap", run @(H RoundRobin Alpha))
      , ("RoundRobin Heap (Merge)", run @(BH RoundRobin Alpha))
      ]
  ] ++
  [ (benchs ++ strats ++ ":", runB args strat)
  | (strats, strat) <-
      [ (" (path)", Path)
      , (" (bloom)", Bloom)
      , (" (pennant)", Pennant)
      , (" (random)", Random)
      ]
  , (benchs, runB) <- reverse
      [ ("Bankers Queue", run @(Q BQueue Alpha))
      , ("Physicists Queue", run @(Q Physicists Alpha))
      , ("Realtime Queue", run @(Q RQueue Alpha))
      , ("Bootstrapped Queue", run @(Q Bootstrapped Alpha))
      , ("Implicit Queue", run @(Q Implicit Alpha))
      , ("Talk Queue", run @(Talk (PrettyCell Int)))
      , ("Bankers Deque", run @(D BDeque Alpha))
      , ("Realtime Deque", run @(D RDeque Alpha))
      , ("Catenable List", run @(D CatDeque Alpha))
      , ("Simple Catenable Deque", run @(D SimpleCat Alpha))
      , ("Implicit Catenable Deque", run @(D ImplicitCat Alpha))
      , ("Catenable List (Concat)", run @(BD CatDeque Alpha))
      , ("Simple Catenable Deque (Concat)", run @(BD SimpleCat Alpha))
      , ("Implicit Catenable Deque (Concat)", run @(BD ImplicitCat Alpha))
      , ("Binomial Heap", run @(H Binomial Alpha))
      , ("ZBinomial Heap", run @(H ZBinomial Alpha))
      , ("Lazy Pairing Heap", run @(H LazyPairing Alpha))
      -- , ("Constant-time Lazy Pairing Heap", run @(H LazyPairingConstant Alpha))
      , ("FIP Lazy Pairing Heap", run @(H LazyPairingFIP Alpha))
      , ("Scheduled Binomial Heap", run @(H Scheduled Alpha))
      , ("Maxiphobic Heap", run @(H Maxiphobic Alpha))
      , ("Binomial Heap (Merge)", run @(BH Binomial Alpha))
      , ("ZBinomial Heap (Merge)", run @(BH ZBinomial Alpha))
      , ("Lazy Pairing Heap (Merge)", run @(BH LazyPairing Alpha))
      -- , ("Constant-time Lazy Pairing Heap (Merge)", run @(BH LazyPairingConstant Alpha))
      , ("FIP Lazy Pairing Heap (Merge)", run @(BH LazyPairingFIP Alpha))
      , ("Scheduled Binomial Heap (Merge)", run @(BH Scheduled Alpha))
      , ("Maxiphobic Heap (Merge)", run @(BH Maxiphobic Alpha))
      , ("Mergesort", run @(S MergeSort Alpha))
      , ("Scheduled Mergesort", run @(S SMergeSort Alpha))
      , ("Binary Random Access List", run @(RA BinaryRA Alpha))
      , ("Zeroless Random Access List", run @(RA ZerolessRA Alpha))
      , ("Finger Tree (Deque)", run @(D FingerDeque Alpha))
      , ("Finger Tree (Concat)", run @(BD FingerDeque Alpha))
      , ("Finger Tree (Heap)", run @(H FingerHeap Alpha))
      , ("Finger Tree (Merge)", run @(BH FingerHeap Alpha))
      , ("Finger Tree (Random Access)", run @(RA FingerRA Alpha))
      , ("Finger Tree (Sortable)", run @(S FingerSort Alpha))
      ]
  ]

main :: IO ()
main = do
  (maxSuccess, maxSize) <- do
    args <- getArgs
    case args of
      [n, s]    -> pure (read n, read s)
      [n]       -> pure (read n, 1000)
      _         -> pure (1000,   1000)
  let args = stdArgs { maxSuccess, maxSize, maxShrinks = maxBound, chatty = False }
  pooledForConcurrently_ (benchmarks args) $ \(s,r) -> do
    res <- r
    putStrLn $ s ++ "\n" ++ output res

-- Categorization of implementations:

-- Passing static credits to static reference:
--  - Realtime Queue (Section 7.2)
--  - Realtime Deque (Section 8.4.3)
--  - Scheduled Binomial Heaps (Section 7.3)
--  - Scheduled Mergesort (Section 7.4)

-- Passing static credits to dynamic reference:
--  - Implicit Queue (Section 11.1)
--  - Binary Random Access List (Section 9.2.3)
--  - Zeroless Random Access List (Section 9.2.3)
--  - Finger Tree
--  - Simple Catenable Deque (Section 11.2)
--  - Implicit Catenable Deque (Section 11.2)

-- Passing dynamic credits to static reference:
--  - Binomial Heaps (Section 6.4.1)
--  - Lazy Pairing Heaps (Section 6.5)
--  - Bottom-up Mergesort (Section 6.4.3)

-- Passing static credits to ghost reference:
--  - Bootstrapped Queue (Section 10.1.3)
--  - Physicists Queue (Section 6.4.2)

-- Requires extra traversal:
--  - Catenable List (Section 10.2.1)

-- Needs Credit Inheritance:
--  - Bankers Queue (Section 6.3.2)
--  - Bankers Deque (Section 8.4.2)