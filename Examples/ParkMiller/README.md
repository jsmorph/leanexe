# ParkMiller: the minimal standard generator

## The generator, its range, and its seed

[The program](Program.lean) is the generator that Park and Miller proposed as a minimal standard in
1988, after Lewis, Goodman, and Miller: `step x = 16807 * x % 2147483647`, with the state in
`[1, 2^31 - 2]`, and `advance n x`, which applies `step` `n` times.  On that range the product is
below `2^46`, so the program computes it in 64-bit words.  Park and Miller give Schrage's method,
which avoids the long product, for 32-bit arithmetic.  `seed s` gives the state for a seed by
the rule of the C++ standard's `linear_congruential_engine` ([rand.eng.lcong]), which
`std::minstd_rand0` instantiates with these parameters: `s % (2^31 - 1)`, or 1 when that is 0.  The
standard's seed has type `uint_fast32_t`, which has at least 32 bits, and 64 under glibc on 64-bit
platforms, so `seed` agrees with the standard for every seed below `2^32`, and for every word on
platforms where that type has 64 bits.  [The compiled module](../../Verified/Examples/ParkMiller.lean) is the verified compiler's
module of the three functions.

## A primitive root and the full period

The modulus `p = 2^31 - 1` is prime, and `p - 1 = 2 · 3^2 · 7 · 11 · 31 · 151 · 331`.  Mathlib's
`lucas_primality` proves the primality of `p` from a witness `a` with `a^(p-1) = 1` in `ZMod p`
and `a^((p-1)/q) ≠ 1` for each prime `q` dividing `p - 1`.  With the witness 16807, the same eight
powers and `orderOf_eq_of_pow_and_pow_div_prime` give 16807 the order `p - 1`, so 16807 is a
primitive root.  Mathlib's `reduce_mod_char` evaluates each power by repeated squaring with a
proof, and `decide +kernel` checks the seven inequalities between residues.  For a state `x` in
the range, `n` steps give `16807^n * x % p`, so `x` returns exactly when the order divides `n`, and
the orbit lemma of [`Examples/Orbit`](../Orbit/README.md) gives each state in the range once per
period.  [The proofs](Period.lean) use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.

| Theorem | Statement |
|---------|-----------|
| `prime_modulus` | `2^31 - 1` is prime. |
| `orderOf_multiplier` | 16807 has order `2^31 - 2` in `ZMod (2^31 - 1)`. |
| `step_minimalPeriod` | From every state in `[1, 2^31 - 2]`, `step` returns after `2^31 - 2` steps and not before. |
| `existsUnique_iterate`, `advance_existsUnique` | From every state in the range, each state in the range occurs at exactly one count below `2^31 - 2`. |
| `advance_mem` | `advance` keeps a state in the range. |
| `seed_mem` | Every seed gives a state in the range. |
| `check_value` | `advance 10000 1 = 1043618065`, the value that Park and Miller give for the 10,000th step and that the C++ standard requires of `minstd_rand0` ([rand.predef]). |
| `step_zero` | 0 is a fixed point of `step`, and `seed` never returns it. |
| `parkMiller_advance` | The module's bytes decode to the module, whose exports compute `advance` and `seed` without a trap, every seed gives a state in the range, and from that state each state in the range occurs at exactly one count below `2^31 - 2`. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Verified.Examples.ParkMiller
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.ParkMiller \
  Verified.Examples.ParkMiller.compiled.module build/verified/parkmiller.wasm
build/tools/leanexe-wasmtime-host call build/verified/parkmiller.wasm advance i64 i64:10000 i64:1
```

The commands build the proofs, write the module, and call `advance 10000 1` in the Wasmtime host,
with the setup of [the repository README](../../README.md#commands).  The call prints 1043618065,
the value of `check_value`.  After `tools/leanrun --memory-high 10G --timeout 12h lake build Verified`,
[`tests/verified/run.sh`](../../tests/verified/run.sh) writes every module of the verified compiler
and compares the cases of [`Verified/Examples/Cases.lean`](../../Verified/Examples/Cases.lean)
between the module and native Lean.

## Related examples

[`Lcg`](../Lcg/README.md) and [`Xorshift`](../Xorshift/README.md) are the other generators, and
[`Orbit`](../Orbit/README.md) holds the lemmas about iterates that the three share.
[`PrimeFactors`](../PrimeFactors/README.md) is another program about primes, a factorization by
trial division.

## References

- P. A. W. Lewis, A. S. Goodman, and J. M. Miller, "A Pseudo-Random Number Generator for the
  System/360," *IBM Systems Journal* 8(2):136–146, 1969,
  [doi:10.1147/sj.82.0136](https://doi.org/10.1147/sj.82.0136).
- S. K. Park and K. W. Miller, "Random Number Generators: Good Ones Are Hard to Find,"
  *Communications of the ACM* 31(10):1192–1201, 1988,
  [doi:10.1145/63039.63042](https://doi.org/10.1145/63039.63042).
- L. Schrage, "A More Portable Fortran Random Number Generator," *ACM Transactions on Mathematical
  Software* 5(2):132–138, 1979, [doi:10.1145/355826.355828](https://doi.org/10.1145/355826.355828).
- ISO/IEC 14882, the C++ standard, [rand.eng.lcong](https://eel.is/c++draft/rand.eng.lcong) and
  [rand.predef](https://eel.is/c++draft/rand.predef).
