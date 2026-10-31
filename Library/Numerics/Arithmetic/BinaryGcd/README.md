# BinaryGcd: Algorithm B of TAOCP §4.5.2

## Request, specification, and program

[The request](request.txt) asks for the greatest common divisor of two words by the binary GCD algorithm, which uses only subtraction, parity tests, and shifts.  [The specification](Spec.lean) states the result with Lean's `Nat.gcd`, as [the Euclidean GCD](../Gcd/README.md) does, so the greatest common divisor of `u` and 0 is `u`, and that of 0 and 0 is 0.

[The program](Program.lean) follows Knuth's steps.  Step B1 halves both arguments while both are even and counts the halvings in `k`, which `commonTwos u v 0` does.  After B1 at least one argument is odd, so removing the factors of 2 from the other, which `removeTwos` does, leaves the greatest common divisor unchanged.  Steps B2 to B6 then hold two odd numbers and replace the larger by their difference with its factors of 2 removed, which is again odd, until the two are equal.  `oddGcd` performs this loop, and `binaryGcd` shifts its result left by `k`.  Knuth's steps hold the difference in one signed variable `t`, while the program keeps the two odd numbers and needs no signed word.  `binaryGcd` returns the other argument when one argument is 0, and `oddGcd` also tests for 0 so that it terminates on every pair of words.  The compiler translates the tail recursions of `removeTwos`, `commonTwos`, and `oddGcd` into loops.

## The bytes compute `Nat.gcd`

`verified_compile compiled := [removeTwos, commonTwos, oddGcd, binaryGcd]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `binaryGcd` is function 5.  The program allocates nothing, so the generated `compiled.binaryGcd.trapFree` excludes a trap without a premise on free memory.

| Theorem | File | Statement |
|---|---|---|
| `removeTwos_spec` | [The proof](Proof.lean) | `x` is `2^j` times `removeTwos x` for some `j`, and `removeTwos x` is odd when `x` is not 0. |
| `commonTwos_spec` | [The proof](Proof.lean) | `commonTwos u v k` divides `u` and `v` by one power `2^j` and adds `j` to `k`, and for nonzero `u` the first quotient is not 0 and the two quotients are not both even. |
| `oddGcd_spec` | [The proof](Proof.lean) | On two odd words, `oddGcd` returns their greatest common divisor. |
| `binaryGcd_eq` | [The proof](Proof.lean) | `binaryGcd u v = expected (u, v)` for every pair of words. |
| `binaryGcd_export` | [The compilation](Compiled.lean) | Export `binaryGcd` of `compiled.module` is function 5. |
| `binaryGcd_callSpec` | [The compilation](Compiled.lean) | From a ready store with room for `compiled.binaryGcd.bound (u, v)` bytes, function 5 returns `expected (u, v)` without a trap and leaves a ready store, as `Verified.CallSpec` states. |
| `binaryGcd_file`, `binaryGcd_file_decode` | [The file theorems](File.lean) | `build/verified/binaryGcd.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`oddGcd_spec` rests on two facts about natural numbers: `gcd u v = gcd u (v - u)` for `u ≤ v`, which Mathlib states as `Nat.gcd_sub_self_right`, and `gcd u (2^j * b) = gcd u b` for odd `u`, since a power of 2 is coprime to an odd number.  `binaryGcd_eq` adds `gcd (2^j * a) (2^j * b) = 2^j * gcd a b` for step B1 and shows that the final shift does not wrap, because the result is at most `u`.  The axiom report of `binaryGcd_callSpec` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.BinaryGcd.Compiled
tests/verified/run.sh --cases binaryGcd
tests/native/verified.sh --module binaryGcd
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../../README.md#commands).  The cases come from `gcdInputs` in [the case inputs](../../../../tests/TestSupport/Modules/BinaryGcd.lean): zeros, ones, `2^64 - 1`, powers of 2 and their neighbors, pairs with a common power of 2, equal pairs, consecutive Fibonacci numbers, and arbitrary words, some shifted left to share factors of 2, each pair in both orders.  [The verified library cases](../../../../tests/TestSupport/LibraryCases.lean) print each pair with `expected`.  [The verified driver](../../../../tests/verified/run.sh) runs the cases in Wasmtime, checks that no call allocates, and checks the file theorems, and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, section 4.5.2](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Josef Stein, Computational problems associated with Racah algebra, Journal of Computational Physics 1 (1967)](https://doi.org/10.1016/0021-9991(67)90047-2)
- [Verified Compiler Manual](../../../../docs/verified-manual.md)
