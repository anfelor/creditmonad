To test our implementations of the data structures, run:

```
stack build && stack exec -- creditmonad 10000 1000 +RTS -N -A64m
```

The first argument (`10000`) is the number of tests to run for each data structure,
while the second argument (`1000`) is the number of operations to perform in each test.
We further instruct the runtime system to use all available cores (`-N`) and 64mb arena size.
With these settings, all tests should finish within ten to twenty minutes.