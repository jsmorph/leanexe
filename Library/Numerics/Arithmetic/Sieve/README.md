# Sieve of Eratosthenes

## Request and specification

[The request](request.txt) asks for the primes below a word `N` in increasing order, computed with the sieve of Eratosthenes, with no allocation but the flags and the result, and with a call stack that does not grow.  [The specification](Spec.lean) states the result as `expected N`, the numbers below `N` that satisfy Mathlib's `Nat.Prime`, in increasing order, as words, so the result for `N` of 0, 1, and 2 is empty.  The specification names the result and not the sieve, and the program text shows the method.  The theorems of the module read the allocation requirement as a call that raises the heap's `top` by at most a block of `N` flags and a block of the result's words, which is weaker than the request, since allocations from free blocks below `top` do not raise it and no theorem states that the call releases the flags.  They read "a call stack that does not grow" as theorems with no call-depth premise.  [The review](review.md) records the specification's two independent reviews and the cases that they added.

## The program

[The program](Program.lean) builds `N` flags, all unset, and `sieveFrom` takes `p` from 2 while `p < N` and `p·p < N`, a test that it makes as `p ≤ (N - 1) / p`, which forms no product, and in which `N - 1` wraps only for `N = 0`, where `p < N` fails.  When the flag of `p` is unset, `crossOff p N` sets the flags of `p·p`, `p·p + p`, and so on below `N`, in a loop of `(N - 1 - p·p) / p + 1` steps whose last index is below `N`.  A flagged `p` is skipped, since a factor of `p` has already set the flags of every multiple of `p` from `p·p`.  `countUnmarked` then counts the unset flags from 2, and `primes` builds an array of that size and fills it in a second pass over the flags with the numbers from 2 whose flags are unset, each at the count of those before it.

The crossing-off sets `⌊(N - 1 - p·p) / p⌋ + 1` flags for each prime `p` with `p·p < N`.  The build writes `N` flags, `countUnmarked` and the filling pass read `N` flags each, and `sieveFrom` reads the flag of each `p` with `p·p < N`.  A flag is a `Bool`, which the module represents as one word, so the flags take `8N` bytes and the result 8 bytes per prime, and each block adds 56 bytes, a header of 48 bytes and a length word.

## The module

`verified_compile compiled := [crossOff, sieveFrom, countUnmarked, primes]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `primes` is function 5.  The compiler translates the tail recursion of `sieveFrom` and the loops of `crossOff`, `countUnmarked`, and `primes` into loops, so no theorem of the module has a call-depth premise.

| Theorem | File | Statement |
|---|---|---|
| `struck_iff` | [The proof](Proof.lean) | Below `n`, a number has a factor `q` with `2 ≤ q` and `q·q` at most the number, `Struck n m`, exactly when it is at least 2 and not prime. |
| `crossOff_spec` | [The proof](Proof.lean) | For `N` flags, `1 ≤ p`, and `p·p < N`, `crossOff p N` keeps `N` flags and sets the flags of the multiples of `p` from `p·p`, and no other. |
| `sieveFrom_spec` | [The proof](Proof.lean) | From `p ≥ 2` with the flags of `Struck p`, the sieve ends with the flags of `Struck N`. |
| `sieve_spec`, `sieve_unset` | [The proof](Proof.lean) | Below `N`, the sieve's flag of `m` is set exactly when `m` is at least 2 and not prime, so the numbers from 2 with unset flags are the primes. |
| `countUnmarked_eq` | [The proof](Proof.lean) | `countUnmarked` counts the primes below `N`. |
| `primes_eq` | [The proof](Proof.lean) | `primes N = expected N` for every word `N`. |
| `primes_export` | [The compilation](Compiled.lean) | Export `primes` of `compiled.module` is function 5. |
| `primes_implements` | [The compilation](Compiled.lean) | Function 5, called with a word `N` from a heap with the allocator invariant, a memory cap of at most 65,535 pages, and room for `compiled.primes.bound N`, returns without a trap the owned array `expected N` and raises `top` by at most the bound. |
| `primes_bound` | [The compilation](Compiled.lean) | `compiled.primes.bound N` is `blockCost N + blockCost (expected N).size`: a block of `N` flags and a block of the result's words. |
| `sieve_file`, `sieve_file_decode` | [The file theorems](File.lean) | `build/verified/sieve.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

In the proof of `sieveFrom_spec`, the flags when the sieve reaches `p` are those of `Struck p m`, a factor `q` of `m` with `2 ≤ q < p` and `q·q ≤ m`.  `Struck (p + 1)` holds for the numbers of `Struck p` and the multiples of `p` from `p·p`, whose flags `crossOff_spec` sets for an unflagged `p`.  A flagged `p` has a factor `q < p` with `q·q ≤ p`, and `q` divides every multiple of `p` from `p·p` with `q·q` below it, so skipping `p` adds nothing.  When the sieve stops, every `q` with `q·q ≤ m < N` lies below `p`, so the flags are those of `Struck N`, and `struck_iff`, with `Nat.minFac` for the converse, makes them the composite numbers.  `primes_implements` composes the generated `compiled.primes.trapFree` with `primes_eq`, and its axiom report names only `propext`, `Classical.choice`, and `Quot.sound`.  Its heap premise needs room for `8N + 8π(N) + 112` bytes below the cap of 65,535 pages, so with `top` at 0 it admits `N` up to about `5.1 × 10^8`, and the theorems say nothing about a larger `N`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.Sieve.Compiled
tests/verified/run.sh --cases sieve
tests/native/verified.sh --module sieve
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../../README.md#commands).  The cases come from `sieveInputs` in [the case inputs](../../../../tests/TestSupport/Modules/Sieve.lean): every `N` from 0 to 30, the squares of the primes from 7 to 37 and of 1,009 and the numbers on either side of each, 64, 128, 1,024, 4,096, 65,536, and 65,537, the powers of 10 from 100 to 1,000,000, whose result holds 78,498 primes, 1,000,004, and 2,000,003.  [The verified library cases](../../../../tests/TestSupport/LibraryCases.lean) print each result with `expected`, whose primality test is Mathlib's.  [The verified driver](../../../../tests/verified/run.sh) runs the cases in Wasmtime and checks that a call makes at most two allocations and leaves one block, the result, and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.  Four more cases expect a trap: `N = 2^29 - 1`, whose flags exceed the memory cap, and `2^29`, `2^32`, and `2^64 - 1`, for which the flags would also hold `2^29` words or more, where the code traps by the rule that the verified compiler's manual states.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, Addison-Wesley, 1997, section 4.5.4](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
