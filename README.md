A Haskell DSL for testing the amortised time complexity of data structures in a persistent setting.
For a high-level description of the library, please see
[Lightweight Testing of Persistent Amortized Time Complexity in the Credit Monad (Haskell Symposium 2025)](https://antonlorenzen.de/papers/creditmonad.pdf).
For formal proofs of correctness, see
[Persistent Amortized Analysis, Operationally (Draft 2026)](https://antonlorenzen.de/papers/persistence-credits.pdf).

To test our implementations of the data structures, run:

```bash
stack build && stack exec -- creditmonad 10000 1000 +RTS -N -A64m
```

The first argument (`10000`) is the number of tests to run for each data structure,
while the second argument (`1000`) is the number of operations to perform in each test.
We further instruct the runtime system to use all available cores (`-N`) and 64 MB arena size.
With these settings, all tests should finish within ten to twenty minutes.

## Implementations

From *Purely Functional Data Structures. Chris Okasaki. Cambridge University Press 1998*:

 * `Test.Credit.Queue.Batched` (Section 5.2)
 * `Test.Credit.Heap.Pairing` (Section 5.5)
 * `Test.Credit.Queue.Bankers` (Section 6.3.2)
 * `Test.Credit.Heap.Binomial` (Section 6.4.1)
 * `Test.Credit.Queue.Physicists` (Section 6.4.2)
 * `Test.Credit.Sortable.MergeSort` (Section 6.4.3)
 * `Test.Credit.Heap.LazyPairing` (Section 6.5)
 * `Test.Credit.Queue.Realtime` (Section 7.2)
 * `Test.Credit.Heap.Scheduled` (Section 7.3)
 * `Test.Credit.Sortable.Scheduled` (Section 7.4)
 * `Test.Credit.Deque.Bankers` (Section 8.4.2)
 * `Test.Credit.Deque.Realtime` (Section 8.4.3)
 * `Test.Credit.RandomAccess.Binary` (Section 9.2.1 and 9.2.3)
 * `Test.Credit.RandomAccess.Zeroless` (Section 9.2.2 and 9.2.3)
 * `Test.Credit.Queue.Bootstrapped` (Section 10.1.3)
 * `Test.Credit.Deque.Catenable` (Section 10.2.1)
 * `Test.Credit.Queue.Implicit` (Section 11.1)
 * `Test.Credit.Deque.SimpleCat` (Section 11.2)
 * `Test.Credit.Deque.ImplicitCat` (Section 11.2)

Other data structures:

 * `Test.Credit.Finger.Original` (Finger trees: a simple general-purpose data structure. Ralf Hinze and Ross Paterson. JFP 2006)
 * `Test.Credit.Finger.Simplified` (Finger trees explained anew, and slightly simplified (functional pearl). Koen Claessen. Haskell Symposium 2020)
 * `Test.Credit.Heap.RoundRobin`, `Test.Credit.Heap.Maxiphobic`, `Test.Credit.Heap.Skew` (Fun with binary heap trees. Chris Okasaki. In The Fun of Programming, Jeremy Gibbons and Oege de Moor (Eds). Palgrave 2003)

Fully In-Place data structures:

 * `Test.Credit.Heap.LazyPairingFIP` (to be published)
 * `Test.Credit.Finger.FIP` (to be published)

## Contributing

While we implement all lazy data structures from Okasaki's book,
we currently do not implement all strict data structures.
In particular, we are missing:

 * Leftist Heaps (Section 3.1)
 * Strict Binomial Heaps (Section 3.2 and 5.3)
 * Red-Black Trees (Section 3.3)
 * Splay Heaps (Section 5.4)
 * Hood-Melville Queues (Section 8.2.1)
 * Skew Binary Random Access Lists (Section 9.3.1)
 * Skew Binomial Heaps (Section 9.3.2)
 * Bootstrapped Random Access Lists (Section 10.1.2)
 * Tries (Section 10.3.1)

We are interested in adding more advanced data structures to the library, such as:

 * Splay Top Trees. Jacob Holm, Eva Rotenberg, and Alice Ryhl. SOSA 2023
 * Pure Binary Finger Search Trees. Gerth Stølting Brodal and Casper Moldrup Rysgaard. SOSA 2025
 * Efficiency of Self-Adjusting Heaps. Corwin Sinnamon and Robert E. Tarjan. TALG 2025
 * Verified persistent catenable deques. Juliette Ponsonnet and François Pottier. JFLA 2026
 * Verified purely functional catenable real-time deques. Jules Viennot, Arthur Wendling, Armaël Guéneau, and François Pottier. Draft 2026