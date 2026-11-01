# MillerRabin: Algorithm A of TAOCP §4.6.3 and Algorithm P of §4.5.4

## Request and specification

[The request](request.txt) asks for modular exponentiation and the strong probable-prime test of Miller and Rabin, Algorithm A of TAOCP §4.6.3 and Algorithm P of §4.5.4, on words, with no product that overflows 64 bits.  [The specification](Spec.lean) states `powModSpec (x, n, m)` as `x^n mod m`, and 0 for `m = 0`, with Lean's `0^0 = 1`, so that `powModSpec (0, 0, m)` is `1 mod m`.  For odd `n ≥ 3`, it writes `n - 1 = 2^k q` with `k` from Mathlib's `padicValNat`.  `StrongProbablePrime n x` holds when `x^q` is 1 modulo `n` or `x^(2^j q)` is `n - 1` modulo `n` for some `j < k`, and `testSpec (n, x)` is 1 exactly then and 0 for even `n` and `n < 3`.  The result depends only on `x mod n`.  A base that `n` divides fails, since 0 is neither 1 nor `n - 1`, the base 1 passes, since `1^q = 1`, and the base `n - 1` passes at `j = 0`, since `q` is odd.  The specification states the test and not primality, since a composite number can pass the test for some bases.  [The review](review.md) records the specification's independent reviews and the classes of input that the cases leave out.

## The program

The product of two residues modulo a word can need 128 bits, so the modular arithmetic of [the program](Program.lean) forms no product and keeps every intermediate value a residue in a word.  `addMod a b m` returns `a - (m - b)` when the sum `a + b` would reach `m` and `a + b` otherwise, so no word wraps.  `mulMod a b m` computes `a * b mod m` by the binary method of §4.6.3 with doubling and addition in place of squaring and multiplication: over the 64 bits of `b`, from the most significant down, it doubles the partial product and adds `a` when the bit is set.  After `i` bits the partial product is `a` times the top `i` bits of `b` modulo `m`, and `mulMod` makes `64 + ν(b)` calls of `addMod`, where `ν(b)` is the number of 1 bits of `b`.

`powMod` is Algorithm A, the right-to-left binary method.  Its loop holds Knuth's `Y` and `Z` as residues, starting at `1 mod m` and `x mod m`, and step `i` multiplies `Y` by `Z` when bit `i` of the exponent is set, as in step A3, and squares `Z`, as in step A5.  After `i` steps `Y = x^(n mod 2^i)` and `Z = x^(2^i)` modulo `m`, the form of Knuth's invariant `x^n = Y Z^N` that the proof uses.  Knuth's step A4 stops when the rest of the exponent is 0, and `powMod` runs over all 64 bits, so for `m > 0` it makes `64 + ν(n)` calls of `mulMod`.  Knuth's algorithm takes a positive exponent, and the start at `1 mod m` gives the exponent 0 its value, which is 0 for `m = 1`.

`test` is Algorithm P with the base as an argument, where step P1 draws a random base `1 < x < n`.  For odd `n ≥ 3`, `twos` counts the `k` low zero bits of `n - 1` in a loop over all 64 bit positions, whose count after `i` positions is `min(i, k)`.  `powMod` raises the base to the odd part `q` of `n - 1`, as in step P2, and `test` returns 1 when the result is 1 or `n - 1`, as in step P3.  Otherwise a loop of 63 steps performs the squarings of step P4, at most `k - 1` of them, and stops squaring when a square is `n - 1`.  `TestInv` states its invariant: after `i` steps the flag is 1 exactly when some `x^(2^j q)` with `1 ≤ j ≤ min(i, k - 1)` is `n - 1` modulo `n`, and while the flag is 0 the state holds `x^(2^min(i, k - 1) q)` modulo `n`.  Knuth's step P3 also stops when a square is 1, after which no square is `n - 1`, and the program continues to square 1 and returns the same answer.  The loop body as written evaluates `mulMod s.1 s.1 n` twice, so the test makes at most `64 + ν(q) + 2(k - 1)` calls of `mulMod`.

## The module computes the results

`verified_compile compiled := [addMod, mulMod, powMod, twos, test]` in [the verified compilation](Compiled.lean) compiles the program into a module whose exports `powMod` and `test` are functions 4 and 6.  The program allocates nothing, so the generated `trapFree` theorems, which [the Verified Compiler Manual](../../../../docs/verified-manual.md#the-implements-and-trapfree-theorems) describes, exclude a trap without a premise on free memory.  `powMod_callSpec` and `test_callSpec` compose those theorems with `powMod_eq` and `test_eq`.

| Theorem | File | Statement |
|---|---|---|
| `addMod_spec`, `mulMod_spec` | [The proof](Proof.lean) | `addMod` gives `(a + b) mod m` for residues `a` and `b`, and `mulMod` gives `a b mod m` for a residue `a`. |
| `powMod_spec`, `powMod_eq` | [The proof](Proof.lean) | `powMod x n m = powModSpec (x, n, m)` for all words. |
| `twos_spec` | [The proof](Proof.lean) | `twos x` is `padicValNat 2 x` for `x > 0`. |
| `testLoop_spec`, `test_eq` | [The proof](Proof.lean) | The squarings of step P4 find `n - 1` exactly when some `x^(2^j q)` with `1 ≤ j < k` is `n - 1` modulo `n`, and `test n x = testSpec (n, x)` for all words. |
| `prime_passes`, `test_prime` | [The proof](Proof.lean) | A prime `n ≥ 3` is a strong probable prime to every base that it does not divide, so `test n x = 1`. |
| `powMod_export`, `test_export` | [The compilation](Compiled.lean) | The exports `powMod` and `test` of `compiled.module` are functions 4 and 6. |
| `powMod_callSpec`, `test_callSpec` | [The compilation](Compiled.lean) | From a ready store with room for the generated bound, functions 4 and 6 return `powModSpec x` and `testSpec x` without a trap and leave a ready store, as `Verified.CallSpec` states. |
| `millerRabin_file`, `millerRabin_file_decode` | [The file theorems](File.lean) | `build/verified/millerRabin.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

`twos_spec` uses Mathlib's facts that `2^k` divides `x` and `2^(k + 1)` does not, so the bits below `k` are 0 and bit `k` is 1.  `prime_passes` works in the field `ZMod n`.  There `x^(n - 1) = 1` by Fermat's little theorem, so the powers `x^(2^j q)` reach 1 by `j = k`.  The power before the first 1 squares to 1 and is not 1, so it is `-1`.  The axiom reports of the call theorems and of `test_prime` name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.MillerRabin.Compiled
tests/verified/run.sh --cases millerRabin
tests/native/verified.sh --module millerRabin
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../../README.md#commands).  The cases come from `powInputs` and `testInputs` in [the case inputs](../../../../tests/TestSupport/Modules/MillerRabin.lean): moduli 0 and 1, the exponents 0 and `2^64 - 1`, moduli near `2^64`, even numbers with bases for which `x^(n - 1)` is 1 modulo `n`, small primes and composites, the Carmichael number 561, strong pseudoprimes that pass at `j = 0`, 1, and 3, primes that pass at `j` up to 58, the bases 0, 1, `n - 1`, and `n` for a prime near `2^64`, numbers whose `n - 1` has 32 and 63 factors 2, a square root of 1 modulo `2^63 + 1` other than 1 and `n - 1`, primes near `2^61` and `2^64`, and arbitrary words.  The specification states `x^n mod m`, which no machine can evaluate for exponents near `2^64`, so the case inputs compute the expected values with `refPow`, repeated squaring, and theorems in the same file show that `powModRef` and `testRef` equal `powModSpec` and `testSpec`.  [The verified driver](../../../../tests/verified/run.sh) runs the cases in Wasmtime, checks that no call allocates, and checks the file theorems, and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, 1997, sections 4.5.4 and 4.6.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Gary L. Miller, Riemann's hypothesis and tests for primality, Journal of Computer and System Sciences 13 (1976)](https://doi.org/10.1016/S0022-0000(76)80043-8)
- [Michael O. Rabin, Probabilistic algorithm for testing primality, Journal of Number Theory 12 (1980)](https://doi.org/10.1016/0022-314X(80)90084-0)
