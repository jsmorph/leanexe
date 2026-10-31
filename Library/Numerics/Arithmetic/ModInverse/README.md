# ModInverse: Algorithm X of TAOCP §4.5.2

## Request, specification, and program

[The request](request.txt) asks for the inverse of a word `a` modulo a word `m`: the `x` with `0 ≤ x < m` and `a * x ≡ 1 (mod m)`, computed with the extended Euclidean algorithm, and 0 when no such `x` exists.  [The specification](Spec.lean) states the inverse with Mathlib's `ZMod m`, the integers modulo `m`: for `m ≥ 2` and `a` coprime to `m`, `expected (a, m)` is the representative in `[0, m)` of the inverse of `a` in `ZMod m`.  Every other pair gives 0.  For `m = 1`, 0 is the inverse of every `a`, since every number is congruent to 1 modulo 1.  For `m = 0`, no number lies in `[0, m)`.  For `m ≥ 2` and `a` with a common factor with `m`, no inverse exists, and 0, which is never an inverse modulo `m ≥ 2`, signals it.

[The program](Program.lean) is Knuth's Algorithm X with only the coefficient of `a`.  The remainders `r0 > r1` start at `m` and `a mod m`, and each step replaces them by `r1` and `r0 mod r1`, as Euclid's algorithm does.  The coefficient of `a` that goes with each remainder alternates in sign, so the program keeps its magnitude and a parity word `p`: when `p = 1`, `a * t1 ≡ r1` and `a * t0 ≡ -r0` modulo `m`, and when `p = 0` the signs are reversed.  Each step sets the new magnitude to `t0 + q * t1`, with `q = r0 / r1`.  The magnitudes satisfy `t1 * r0 + t0 * r1 = m`, so none exceeds `m` and no word operation wraps.  When `r1` reaches 0, `r0` is the greatest common divisor of `a` and `m`, and when it is 1 the inverse is `t0` or `m - t0`, by the parity.  `modInverse` returns 0 for `m ≤ 1` and otherwise starts `euclid` at `(m, a mod m, 0, 1)` with `p = 1`.  The compiler translates the tail recursion of `euclid` into a loop.

## The module computes the inverse

`verified_compile compiled := [euclid, modInverse]` in [the verified compilation](Compiled.lean) compiles the program into a module whose export `modInverse` is function 3.  The program allocates nothing, so the generated `compiled.modInverse.trapFree` excludes a trap without a premise on free memory.

| Theorem | File | Statement |
|---|---|---|
| `euclid_spec` | [The proof](Proof.lean) | From a state that meets the invariant, the loop returns, when `gcd a m = 1`, a word `x < m` with `a * x = 1` in `ZMod m`, and 0 otherwise. |
| `val_inv_eq` | [The proof](Proof.lean) | For `a` coprime to `m`, a number `x < m` with `a * x = 1` in `ZMod m` is the value of the inverse of `a` in `ZMod m`. |
| `modInverse_eq` | [The proof](Proof.lean) | `modInverse a m = expected (a, m)` for every pair of words. |
| `modInverse_export` | [The compilation](Compiled.lean) | Export `modInverse` of `compiled.module` is function 3. |
| `modInverse_callSpec` | [The compilation](Compiled.lean) | From a ready store with room for `compiled.modInverse.bound (a, m)` bytes, function 3 returns `expected (a, m)` without a trap and leaves a ready store, as `Verified.CallSpec` states. |
| `modInverse_file`, `modInverse_file_decode` | [The file theorems](File.lean) | `build/verified/modInverse.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`euclid_spec` carries five facts from step to step: the identity `t1 * r0 + t0 * r1 = m`, `r1 < r0`, `t0 ≤ t1`, `gcd r0 r1 = gcd a m`, and the two congruences in `ZMod m` with the sign that `p` encodes.  The identity gives the bound that keeps each word operation exact, and `linear_combination` checks each step's congruences.  The axiom report of `modInverse_callSpec` names only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.ModInverse.Compiled
tests/verified/run.sh --cases modInverse
tests/native/verified.sh --module modInverse
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../../README.md#commands).  The cases come from `inverseInputs` in [the case inputs](../../../../tests/TestSupport/Modules/ModInverse.lean): the moduli 0 and 1 with several words, small moduli with every `a` below them and a few above, and large moduli, among them the primes `2^61 - 1` and `2^64 - 59`, the odd modulus `2^64 - 1`, and the even modulus `2^63`, with 0, 1, 2, `m - 1`, `m`, `m + 1`, `2^64 - 1`, and arbitrary words.  [The review](review.md) records the specification's two independent reviews and the classes of input that the cases leave out.  [The verified library cases](../../../../tests/TestSupport/LibraryCases.lean) print each pair with `expected`.  [The verified driver](../../../../tests/verified/run.sh) runs the cases in Wasmtime, checks that no call allocates, and checks the file theorems, and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, section 4.5.2, and Volume 1: Fundamental Algorithms, third edition, section 1.2.1](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Mathlib: Mathlib.Data.ZMod.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html)
- [Verified Compiler Manual](../../../../docs/verified-manual.md)
