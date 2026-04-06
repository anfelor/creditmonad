{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, DerivingStrategies #-}

module Main where

import UnliftIO.Internals.Async
import UnliftIO.MVar (newMVar, withMVar)
import System.Environment (getArgs)
import Test.QuickCheck
import Prettyprinter

import Control.Monad
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
import Test.Credit.Finger.Base
import Test.Credit.Finger.FIP
import Test.Credit.Finger.Original
import Test.Credit.Finger.Simplified
import Test.Credit.Heap.Base
import Test.Credit.Heap.Binomial
import Test.Credit.Heap.ZBinomial
import Test.Credit.Heap.LazyPairing
import Test.Credit.Heap.LazyPairingFIP
import Test.Credit.Heap.Pairing
import Test.Credit.Heap.Scheduled
import Test.Credit.Heap.Maxiphobic
import Test.Credit.Heap.RoundRobin
import Test.Credit.Heap.Skew
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
      , ("FIP Lazy Pairing Heap", run @(H LazyPairingFIP Alpha))
      , ("Scheduled Binomial Heap", run @(H Scheduled Alpha))
      , ("Maxiphobic Heap", run @(H Maxiphobic Alpha))
      , ("Skew Heap", run @(H Skew Alpha))
      , ("Binomial Heap (Merge)", run @(BH Binomial Alpha))
      , ("ZBinomial Heap (Merge)", run @(BH ZBinomial Alpha))
      , ("Lazy Pairing Heap (Merge)", run @(BH LazyPairing Alpha))
      , ("FIP Lazy Pairing Heap (Merge)", run @(BH LazyPairingFIP Alpha))
      , ("Scheduled Binomial Heap (Merge)", run @(BH Scheduled Alpha))
      , ("Maxiphobic Heap (Merge)", run @(BH Maxiphobic Alpha))
      , ("Skew Heap (Merge)", run @(BH Skew Alpha))
      , ("Mergesort", run @(S MergeSort Alpha))
      , ("Scheduled Mergesort", run @(S SMergeSort Alpha))
      , ("Binary Random Access List", run @(RA BinaryRA Alpha))
      , ("Zeroless Random Access List", run @(RA ZerolessRA Alpha))
      , ("Simplified Finger Tree (Deque)", run @(D (FingerDeque Simplified) Alpha))
      , ("Simplified Finger Tree (Concat)", run @(BD (FingerDeque Simplified) Alpha))
      , ("Simplified Finger Tree (Heap)", run @(H (FingerHeap Simplified) Alpha))
      , ("Simplified Finger Tree (Merge)", run @(BH (FingerHeap Simplified) Alpha))
      , ("Simplified Finger Tree (Random Access)", run @(RA (FingerRA Simplified) Alpha))
      , ("Simplified Finger Tree (Sortable)", run @(S (FingerSort Simplified) Alpha))
      , ("Original Finger Tree (Deque)", run @(D (FingerDeque Original) Alpha))
      , ("Original Finger Tree (Concat)", run @(BD (FingerDeque Original) Alpha))
      , ("Original Finger Tree (Heap)", run @(H (FingerHeap Original) Alpha))
      , ("Original Finger Tree (Merge)", run @(BH (FingerHeap Original) Alpha))
      , ("Original Finger Tree (Random Access)", run @(RA (FingerRA Original) Alpha))
      , ("Original Finger Tree (Sortable)", run @(S (FingerSort Original) Alpha))
      , ("FIP Finger Tree (Deque)", run @(D (FingerDeque FIP) Alpha))
      , ("FIP Finger Tree (Concat)", run @(BD (FingerDeque FIP) Alpha))
      , ("FIP Finger Tree (Heap)", run @(H (FingerHeap FIP) Alpha))
      , ("FIP Finger Tree (Merge)", run @(BH (FingerHeap FIP) Alpha))
      , ("FIP Finger Tree (Random Access)", run @(RA (FingerRA FIP) Alpha))
      , ("FIP Finger Tree (Sortable)", run @(S (FingerSort FIP) Alpha))
      ]
  ]

tests :: Args -> [(String, IO Result)]
tests args =
  [ (testName ++ ":", quickCheckWithResult args testProp)
  | (testName, testProp) <- reverse
      [ ("Batched Queue", test @(Q Batched Alpha))
      , ("Pairing Heap", test @(H Pairing Alpha))
      , ("Pairing Heap (Merge)", test @(BH Pairing Alpha))
      , ("RoundRobin Heap", test @(H RoundRobin Alpha))
      , ("RoundRobin Heap (Merge)", test @(BH RoundRobin Alpha))
      ]
  ] ++
  [ (testName ++ ":", quickCheckWithResult args testProp)
  | (testName, testProp) <- reverse
      [ ("Bankers Queue", test @(Q BQueue Alpha))
      , ("Physicists Queue", test @(Q Physicists Alpha))
      , ("Realtime Queue", test @(Q RQueue Alpha))
      , ("Bootstrapped Queue", test @(Q Bootstrapped Alpha))
      , ("Implicit Queue", test @(Q Implicit Alpha))
      , ("Bankers Deque", test @(D BDeque Alpha))
      , ("Realtime Deque", test @(D RDeque Alpha))
      -- Catenable lists do not implement unsnoc properly,
      --   so this test runs out of stack.
      -- , ("Catenable List", test @(D CatDeque Alpha))
      , ("Simple Catenable Deque", test @(D SimpleCat Alpha))
      , ("Implicit Catenable Deque", test @(D ImplicitCat Alpha))
      , ("Catenable List (Concat)", test @(BD CatDeque Alpha))
      , ("Simple Catenable Deque (Concat)", test @(BD SimpleCat Alpha))
      , ("Implicit Catenable Deque (Concat)", test @(BD ImplicitCat Alpha))
      , ("Binomial Heap", test @(H Binomial Alpha))
      , ("ZBinomial Heap", test @(H ZBinomial Alpha))
      , ("Lazy Pairing Heap", test @(H LazyPairing Alpha))
      , ("FIP Lazy Pairing Heap", test @(H LazyPairingFIP Alpha))
      , ("Scheduled Binomial Heap", test @(H Scheduled Alpha))
      , ("Maxiphobic Heap", test @(H Maxiphobic Alpha))
      , ("Skew Heap", test @(H Skew Alpha))
      , ("Binomial Heap (Merge)", test @(BH Binomial Alpha))
      , ("ZBinomial Heap (Merge)", test @(BH ZBinomial Alpha))
      , ("Lazy Pairing Heap (Merge)", test @(BH LazyPairing Alpha))
      , ("FIP Lazy Pairing Heap (Merge)", test @(BH LazyPairingFIP Alpha))
      , ("Scheduled Binomial Heap (Merge)", test @(BH Scheduled Alpha))
      , ("Maxiphobic Heap (Merge)", test @(BH Maxiphobic Alpha))
      , ("Skew Heap (Merge)", test @(BH Skew Alpha))
      , ("Mergesort", test @(S MergeSort Alpha))
      , ("Scheduled Mergesort", test @(S SMergeSort Alpha))
      , ("Binary Random Access List", test @(RA BinaryRA Alpha))
      , ("Zeroless Random Access List", test @(RA ZerolessRA Alpha))
      , ("Simplified Finger Tree (Deque)", test @(D (FingerDeque Simplified) Alpha))
      , ("Simplified Finger Tree (Concat)", test @(BD (FingerDeque Simplified) Alpha))
      , ("Simplified Finger Tree (Heap)", test @(H (FingerHeap Simplified) Alpha))
      , ("Simplified Finger Tree (Merge)", test @(BH (FingerHeap Simplified) Alpha))
      , ("Simplified Finger Tree (Random Access)", test @(RA (FingerRA Simplified) Alpha))
      , ("Simplified Finger Tree (Sortable)", test @(S (FingerSort Simplified) Alpha))
      , ("Original Finger Tree (Deque)", test @(D (FingerDeque Original) Alpha))
      , ("Original Finger Tree (Concat)", test @(BD (FingerDeque Original) Alpha))
      , ("Original Finger Tree (Heap)", test @(H (FingerHeap Original) Alpha))
      , ("Original Finger Tree (Merge)", test @(BH (FingerHeap Original) Alpha))
      , ("Original Finger Tree (Random Access)", test @(RA (FingerRA Original) Alpha))
      , ("Original Finger Tree (Sortable)", test @(S (FingerSort Original) Alpha))
      , ("FIP Finger Tree (Deque)", test @(D (FingerDeque FIP) Alpha))
      , ("FIP Finger Tree (Concat)", test @(BD (FingerDeque FIP) Alpha))
      , ("FIP Finger Tree (Heap)", test @(H (FingerHeap FIP) Alpha))
      , ("FIP Finger Tree (Merge)", test @(BH (FingerHeap FIP) Alpha))
      , ("FIP Finger Tree (Random Access)", test @(RA (FingerRA FIP) Alpha))
      , ("FIP Finger Tree (Sortable)", test @(S (FingerSort FIP) Alpha))
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
  let benchArgs = stdArgs { maxSuccess, maxSize, maxShrinks = maxBound, chatty = False }
  let testArgs = benchArgs { maxSuccess = maxSuccess `div` 10, maxSize = maxSize `div` 10 }
  when (maxSuccess <= 1000 && maxSize <= 100) $
    putStrLn $ "Small test size: only reporting failed tests."
  consoleLock <- newMVar ()
  pooledForConcurrently_ (tests testArgs ++ benchmarks benchArgs) $ \(s,r) -> do
    res <- r
    unless (isSuccess res && (maxSuccess <= 1000 && maxSize <= 100)) $
      withMVar consoleLock $ const $ putStrLn $ s ++ "\n" ++ output res