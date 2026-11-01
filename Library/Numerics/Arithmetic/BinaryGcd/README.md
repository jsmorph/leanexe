# BinaryGcd: Algorithm B of TAOCP §4.5.2

## Request and specification

[The request](request.txt) asks for the greatest common divisor of two words by the binary GCD algorithm, Algorithm B of TAOCP §4.5.2, which uses only subtraction, parity tests, and shifts.  [The specification](Spec.lean) states the result with Lean's `Nat.gcd`, as [the Euclidean GCD](../Gcd/README.md) does, so the greatest common divisor of `u` and 0 is `u`, and that of 0 and 0 is 0.  The specification fixes the result and not the method, so only the program text shows that the module performs Algorithm B.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.

## The program

[The program](Program.lean) is Algorithm B on words.  `commonTwos u v 0` performs step B1: it halves both arguments while both are even and counts the halvings in `k`.  At least one quotient is then odd, and the first pass of steps B2 to B5 removes the factors of 2 from the other, which `binaryGcd` does by applying `removeTwos`, Knuth's steps B3 and B4, to both.  `oddGcd` performs step B6 and the later passes of steps B3 to B5: while its two odd numbers differ, it replaces the larger by their difference with the factors of 2 removed, and `binaryGcd` shifts the common value left by `k`.  The compiler translates the tail recursions of `removeTwos`, `commonTwos`, and `oddGcd` into loops.

The loop of `oddGcd` keeps both numbers odd and their greatest common divisor unchanged, and `oddGcd_spec` proves its result by induction on that recursion.  Knuth holds the difference in one signed variable `t` and uses its sign to choose which of `u` and `v` to replace, while the program keeps the two odd numbers in unsigned words, compares them, and subtracts the smaller from the larger, so no subtraction wraps.  Knuth stops when `t = u - v` is 0, and `oddGcd` tests `u = v` before it subtracts.  Knuth's algorithm takes positive integers, while `binaryGcd` returns the other argument when one is 0, and the tests for 0 in `removeTwos`, `commonTwos`, and `oddGcd` make each of them terminate on every word.

Each pass of `oddGcd` that subtracts replaces the larger odd number `L` by at most `(L - S)/2`, where `S` is the smaller, so the sum of the two numbers at least halves, and the sum stays at least 2.  For nonzero `u` and `v`, `oddGcd` makes at most `⌊lg max(u, v)⌋` subtractions, 63 on words, and the pair `(1, 2^64 - 1)` takes all 63.  A subtraction does not lengthen the larger number, a halving shortens one number by one bit, and both numbers keep at least one bit, so for nonzero `u` and `v` the program makes at most `⌊lg u⌋ + ⌊lg v⌋` halvings in all, counting two for each pass of step B1.

## The bytes compute `Nat.gcd`

`verified_compile compiled := [removeTwos, commonTwos, oddGcd, binaryGcd]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `binaryGcd` is function 5.  The compiler generates the theorems that [the Verified Compiler Manual](../../../../docs/verified-manual.md#the-implements-and-trapfree-theorems) describes: `compiled.binaryGcd.implements`, which states that the module computes `binaryGcd`, and `compiled.binaryGcd.trapFree`.  The program allocates nothing, so `compiled.binaryGcd.trapFree` excludes a trap without a premise on free memory.

| Theorem | File | Statement |
|---|---|---|
| `removeTwos_spec` | [The proof](Proof.lean) | `x` is `2^j` times `removeTwos x` for some `j`, and `removeTwos x` is odd when `x` is not 0. |
| `commonTwos_spec` | [The proof](Proof.lean) | `commonTwos u v k` divides `u` and `v` by one power `2^j` and adds `j` to `k`, and for nonzero `u` the first quotient is not 0 and the two quotients are not both even. |
| `oddGcd_spec` | [The proof](Proof.lean) | On two odd words, `oddGcd` returns their greatest common divisor. |
| `binaryGcd_eq` | [The proof](Proof.lean) | `binaryGcd u v = expected (u, v)` for every pair of words. |
| `binaryGcd_export` | [The compilation](Compiled.lean) | Export `binaryGcd` of `compiled.module` is function 5. |
| `binaryGcd_callSpec` | [The compilation](Compiled.lean) | From a ready store with room for `compiled.binaryGcd.bound (u, v)` bytes, function 5 returns `expected (u, v)` without a trap and leaves a ready store, as `Verified.CallSpec` states. |
| `binaryGcd_file`, `binaryGcd_file_decode` | [The file theorems](File.lean) | `build/verified/binaryGcd.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`oddGcd_spec` uses two facts about natural numbers: `gcd u v = gcd u (v - u)` for `u ≤ v`, which Lean's core library states as `Nat.gcd_sub_self_right`, and `gcd u (2^j * b) = gcd u b` for odd `u`, since a power of 2 is coprime to an odd number.  `binaryGcd_eq` adds `gcd (2^j * a) (2^j * b) = 2^j * gcd a b` for step B1 and shows that the final shift does not wrap, because the result is at most `u`.  The axiom report of `binaryGcd_callSpec` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.BinaryGcd.Compiled
tests/verified/run.sh --cases binaryGcd
tests/native/verified.sh --module binaryGcd
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../../README.md#commands).  The cases come from `gcdInputs` in [the case inputs](../../../../tests/TestSupport/Modules/BinaryGcd.lean): zeros, ones, `2^64 - 1`, powers of 2 and their neighbors, pairs with a common power of 2, equal pairs, consecutive Fibonacci numbers, and arbitrary words, some shifted left to share factors of 2, each pair in both orders.  [The verified library cases](../../../../tests/TestSupport/LibraryCases.lean) print each pair with `expected`.  [The verified driver](../../../../tests/verified/run.sh) runs the cases in Wasmtime, checks that no call allocates, and checks the file theorems, and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, 1997, section 4.5.2](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
