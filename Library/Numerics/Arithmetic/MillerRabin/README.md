# MillerRabin: Algorithm A of TAOCP §4.6.3 and Algorithm P of §4.5.4

## Request, specification, and program

[The request](request.txt) asks for modular exponentiation and the strong probable-prime test of Miller and Rabin on words, with no product that overflows 64 bits.  [The specification](Spec.lean) states `powModSpec (x, n, m)` as `x^n mod m`, and 0 for `m = 0`, with Lean's `0^0 = 1`, so that `powModSpec (0, 0, m)` is `1 mod m`.  For odd `n ≥ 3`, it writes `n - 1 = 2^k q` with `k` from Mathlib's `padicValNat`.  `StrongProbablePrime n x` holds when `x^q` is 1 modulo `n` or `x^(2^j q)` is `n - 1` modulo `n` for some `j < k`, and `testSpec (n, x)` is 1 exactly then and 0 for even `n` and `n < 3`.  The result depends only on `x mod n`, so a base that `n` divides fails, and the bases 1 and `n - 1` pass.  The specification states the test and not primality, since a composite number can pass the test for some bases.

[The program](Program.lean) keeps every value a residue modulo `m`.  `addMod a b m` adds two residues and subtracts `m - b` when the sum would reach `m`, so no word wraps.  `mulMod a b m` multiplies by the binary method on the bits of `b`, from the most significant down: it doubles the partial product and adds `a` for each set bit, each step with `addMod`.  `powMod` is Algorithm A, the right-to-left binary method, over the 64 bits of the exponent: it squares the power `Z` at each bit and multiplies it into the product `Y` when the bit is set.  `twos` counts the low zero bits of `n - 1`.  `test` is Algorithm P: it raises the base to the odd part `q`, answers 1 when the result is 1 or `n - 1`, and otherwise squares it up to `k - 1` times, looking for `n - 1`.  Knuth's Algorithm P also stops when the result becomes 1, after which no square is `n - 1`, so the program's answer is the same without that stop.

## The module computes the results

`verified_compile compiled := [addMod, mulMod, powMod, twos, test]` in [the verified compilation](Compiled.lean) compiles the program into a module whose exports `powMod` and `test` are functions 4 and 6.  The program allocates nothing, so the generated `trapFree` theorems exclude a trap without a premise on free memory.

| Theorem | File | Statement |
|---|---|---|
| `addMod_spec`, `mulMod_spec` | [The proof](Proof.lean) | `addMod` and `mulMod` give `(a + b) mod m` and `a b mod m` for residues `a`. |
| `powMod_spec`, `powMod_eq` | [The proof](Proof.lean) | `powMod x n m = powModSpec (x, n, m)` for all words. |
| `twos_spec` | [The proof](Proof.lean) | `twos x` is `padicValNat 2 x` for `x > 0`. |
| `testLoop_spec`, `test_eq` | [The proof](Proof.lean) | The squarings of step P4 find `n - 1` exactly when some `x^(2^j q)` with `1 ≤ j < k` is `n - 1` modulo `n`, and `test n x = testSpec (n, x)` for all words. |
| `prime_passes`, `test_prime` | [The proof](Proof.lean) | A prime `n ≥ 3` is a strong probable prime to every base that it does not divide, so `test n x = 1`. |
| `powMod_export`, `test_export` | [The compilation](Compiled.lean) | The exports `powMod` and `test` of `compiled.module` are functions 4 and 6. |
| `powMod_callSpec`, `test_callSpec` | [The compilation](Compiled.lean) | From a ready store with room for the generated bound, functions 4 and 6 return `powModSpec x` and `testSpec x` without a trap and leave a ready store, as `Verified.CallSpec` states. |
| `millerRabin_file`, `millerRabin_file_decode` | [The file theorems](File.lean) | `build/verified/millerRabin.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`. |

The loop of `mulMod` keeps `a` times the top `i` bits of `b` modulo `m`, and the loop of `powMod` keeps `Y = x^(n mod 2^i)` and `Z = x^(2^i)` modulo `m`.  `twos_spec` uses Mathlib's facts that `2^k` divides `x` and `2^(k + 1)` does not, so the bits below `k` are 0 and bit `k` is 1.  `TestInv` states the invariant of the squarings: a flag records whether some power from `x^(2q)` to `x^(2^min(j, k-1) q)` was `n - 1`, and while it is 0 the last power is the current residue.  `prime_passes` works in the field `ZMod n`.  There `x^(n - 1) = 1` by Fermat's little theorem, so the powers `x^(2^j q)` reach 1 by `j = k`.  The power before the first 1 squares to 1 and is not 1, so it is `-1`.  The axiom reports of the call theorems and of `test_prime` name only `propext`, `Classical.choice`, and `Quot.sound`.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Arithmetic.MillerRabin.Compiled
tests/verified/run.sh --cases millerRabin
tests/native/verified.sh --module millerRabin
```

The commands build the verified compilation and its theorems and run the module's cases, with the setup of [the repository README](../../../../README.md#commands).  The cases come from `powInputs` and `testInputs` in [the case inputs](../../../../tests/TestSupport/Modules/MillerRabin.lean): moduli 0 and 1, the exponents 0 and `2^64 - 1`, moduli near `2^64`, even numbers with bases for which `x^(n - 1)` is 1 modulo `n`, small primes and composites, the Carmichael number 561, strong pseudoprimes that pass at `j = 0`, 1, and 3, primes that pass at `j` up to 58, the bases 0, 1, `n - 1`, and `n` for a prime near `2^64`, numbers whose `n - 1` has 32 and 63 factors 2, a square root of 1 modulo `2^63 + 1` other than 1 and `n - 1`, primes near `2^61` and `2^64`, and arbitrary words.  The specification states `x^n mod m`, which no machine can evaluate for exponents near `2^64`, so the case inputs compute the expected values with `refPow`, repeated squaring, and theorems in the same file show that `powModRef` and `testRef` equal `powModSpec` and `testSpec`.  [The review](review.md) records the specification's independent reviews and the classes of input that the cases leave out.  [The verified driver](../../../../tests/verified/run.sh) runs the cases in Wasmtime, checks that no call allocates, and checks the file theorems, and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled with CompCert.

## References

- [Donald E. Knuth, The Art of Computer Programming, Volume 2: Seminumerical Algorithms, third edition, sections 4.5.4 and 4.6.3](https://www-cs-faculty.stanford.edu/~knuth/taocp.html)
- [Michael O. Rabin, Probabilistic algorithm for testing primality, Journal of Number Theory 12 (1980)](https://doi.org/10.1016/0022-314X(80)90084-0)
- [Verified Compiler Manual](../../../../docs/verified-manual.md)
