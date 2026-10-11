# Lcg: a linear congruential generator modulo 2^64

## What it is

[The program](Program.lean) is the linear congruential generator `affine a c x = a * x + c`
modulo `2^64`, with `step = affine 6364136223846793005 1442695040888963407`, and `advance n x`,
which applies `step` `n` times with `LeanExe.loop`.  The multiplier is the one that the MMIX
Supplement's `rsixfour.c` attributes to Knuth, *The Art of Computer Programming*, Volume 2,
Section 3.3.4, page 108.  The increment is `PCG_DEFAULT_INCREMENT_64` of O'Neill's PCG library,
which pairs it with the same multiplier, and secondary sources call the pair Knuth's MMIX generator.
`rsixfour.c` itself uses the increment `9754186451795953191`, and `minimalPeriod_affine_iff` gives
the full period for any odd increment with this multiplier.  [The compiled module](../../Verified/Examples/Lcg.lean) is the verified compiler's
module of the three functions.

## What it shows

Hull and Dobell's theorem, Theorem A of Knuth's Section 3.2.1.2, states that an LCG modulo `m` has
period `m` if and only if `c` is prime to `m`, `a - 1` is divisible by every prime factor of `m`,
and `a - 1` is divisible by 4 when `m` is.  For `m = 2^64` the conditions are `c % 2 = 1` and
`a % 4 = 1`.  [The proofs](Period.lean) compute the iterates of `affine a c` by squaring.  `2^k`
steps form the affine map with coefficients `doubled a c k`, where squaring takes `(b, d)` to
`(b * b, (b + 1) * d)`.  Under the conditions, induction with `ring` shows `b = 1 + 2^(k+2) * t`
and `d = 2^k * (2 * s + 1)` for some words `t` and `s`.  At `k = 64` the map is the identity, and
at `k = 63` it adds `2^63`, so Mathlib's `minimalPeriod_eq_prime_pow` gives the minimal period
`2^64` at every word.

For necessity, reduction modulo 4 is a ring homomorphism from words to `ZMod 4`, and a point of
period `2^64` reaches every word, so the reduced affine map reaches every residue.  `decide` checks
all 64 choices of coefficients and start in `ZMod 4`: when the coefficients fail the conditions,
the orbit stays among its first four iterates and misses a residue.  For the bits, `2^k` steps add
`2^k` plus a multiple of `2^(k+1)`, which complements bit `k`, and the 2-adic valuation of a
candidate period finishes the argument.  The bit theorem states the generator's known weakness:
bit 0 alternates, and only bit 63 has the full period.

| Theorem | Statement |
|---------|-----------|
| `minimalPeriod_affine_iff` | `minimalPeriod (affine a c) x = 2^64 ↔ a % 4 = 1 ∧ c % 2 = 1`, for every `a`, `c`, `x`. |
| `step_minimalPeriod` | From every word, `step` returns after `2^64` steps and not before. |
| `step_bijective` | `step` is a bijection on words. |
| `advance_existsUnique` | For all words `x` and `y`, exactly one count `n : UInt64` gives `advance n x = y`. |
| `advance_ne_self` | `advance n x ≠ x` for every nonzero count `n`. |
| `periodic_testBit_iff`, `step_periodic_testBit_iff` | Bit `k` of the state, for `k < 64`, repeats after `p` steps if and only if `2^(k+1)` divides `p`. |
| `lcg_advance` | The module's bytes decode to the module, whose `advance` export computes `advance` without a trap, and for all words `x` and `y` exactly one count `n` gives `advance n x = y`. |

The proofs use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  Finite checks use
`decide` or `decide +kernel`, which the kernel evaluates without adding an axiom.

## Running it

```sh
tools/leanrun --timeout 60m lake build Verified.Examples.Lcg
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.Lcg \
  Verified.Examples.Lcg.compiled.module build/verified/lcg.wasm
build/tools/leanexe-wasmtime-host call build/verified/lcg.wasm advance i64 i64:1 i64:0
```

The commands build the proofs, write the module, and call `advance 1 0` in the Wasmtime host, with
the setup of [the repository README](../../README.md#commands).  The call prints
1442695040888963407, the increment, which one step adds to the state 0.  After
`tools/leanrun --timeout 60m lake build Verified`,
[`tests/verified/run.sh`](../../tests/verified/run.sh) writes every module of the verified compiler
and compares the cases of [`Verified/Examples/Cases.lean`](../../Verified/Examples/Cases.lean)
between the module and native Lean.

## Related examples

[`ParkMiller`](../ParkMiller/README.md) and [`Xorshift`](../Xorshift/README.md) are the other
generators, and [`Orbit`](../Orbit/README.md) holds the lemmas about iterates that the three share.
[SplitMix64](../Prng/README.md) advances a Weyl sequence, the case `a = 1` of `affine`, and mixes
the state into its output.

## References

- T. E. Hull and A. R. Dobell, "Random Number Generators," *SIAM Review* 4(3):230–254, 1962,
  [doi:10.1137/1004061](https://doi.org/10.1137/1004061).
- D. E. Knuth, *The Art of Computer Programming*, Volume 2, *Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, Sections 3.2.1.2 and 3.3.4.
- M. Ruckert, [`rsixfour.c`](https://mmix.cs.hm.edu/tools/rsixfour.c), from the [MMIX
  Supplement](https://mmix.cs.hm.edu/supplement/index.html).
- M. E. O'Neill, "PCG: A Family of Simple Fast Space-Efficient Statistically Good Algorithms for
  Random Number Generation," Harvey Mudd College, HMC-CS-2014-0905, 2014, and
  [`pcg_variants.h`](https://github.com/imneme/pcg-c/blob/master/include/pcg_variants.h).
