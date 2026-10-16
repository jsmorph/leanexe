# Lcg: a linear congruential generator modulo 2^64

## What it is

[The program](Program.lean) is the linear congruential generator `affine a c x = a * x + c`
modulo `2^64`, with `step = affine multiplier increment`, `multiplier = 6364136223846793005`, and
`increment = 1442695040888963407`.  `advance n x` applies `step` `n` times with `LeanExe.loop`, and
`jump n x` computes the same state by Brown's jump-ahead, 64 passes of `jumpPass`.  The multiplier
is the one that the MMIX Supplement's `rsixfour.c` attributes to Knuth, *The Art of Computer
Programming*, Volume 2, Section 3.3.4, page 108.  The increment is `PCG_DEFAULT_INCREMENT_64` of
O'Neill's PCG library, which pairs it with the same multiplier, and secondary sources call the pair
Knuth's MMIX generator.  `rsixfour.c` itself uses the increment `9754186451795953191`, and
`minimalPeriod_affine_iff` gives the full period for any odd increment with this multiplier.  [The
compiled module](../../Verified/Examples/Lcg.lean) is the verified compiler's module of `affine`,
`step`, `advance`, `jumpPass`, and `jump`.

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

At pass `i`, `jump` holds the coefficients `(am, ap)` of `step^[n % 2^i]` and `(cm, cp)` of
`step^[2^i]`.  When bit `i` of `n` is set, the pass applies `step^[2^i]` after `step^[n % 2^i]`,
and it squares the map of `2^i` steps to `(cm * cm, (cm + 1) * cp)`, the squaring of `doubled`, so
[the jump proof](Jump.lean) follows from `iterate_two_pow` by induction on the passes.  Since
`n ↦ advance n x` is a bijection of the words, the top `j` bits of the state take each
value `2^(64 - j)` times over a period, from the count of words with given top bits in
[`Examples/Orbit`](../Orbit/README.md).

[The lattice proofs](Lattice.lean) describe the tuples `(x, step x, …, step^[t-1] x)` of `t`
successive states.  An integer vector `s` lies in the dual lattice `Dual t` when
`∑ s_k a^k ≡ 0 (mod 2^64)`, for `a` the multiplier, and since `k` steps from `x` give `a^k x` plus
`k` steps from 0, `∑ s_k y_k` at every tuple `y` is congruent modulo `2^64` to its value `d` at the
tuple from 0.  The tuples therefore lie on parallel hyperplanes `∑ s_k y_k = d + j 2^64` for
integers `j`, and for a nonzero `s` at most `∑ |s_k|` of them hold tuples.  With the shortest
vectors of `Dual t` for two to five states and, for six, a vector whose sum of magnitudes, 2,296, is
below the 2,818 of the shortest, all pairs of successive states lie on at most 4,008,749,872 lines
and all 6-tuples on at most 2,296 hyperplanes, from every starting word.

[The spectral test](Spectral.lean) gives `ν_t²`, the smallest squared length of a nonzero vector
of `Dual t`, for `t = 2, …, 6`: 8,810,664,174,654,508,192, 6,398,304,806,574, 4,112,636,266,
45,662,836, and 1,846,368, or `log2 ν_t` of 31.47, 21.27, 15.97, 12.72, and 10.41.  Knuth shows
that `1 / ν_t` is the largest distance between adjacent hyperplanes, over all families of parallel
hyperplanes that cover the `t`-tuples, scaled to the unit cube.  A shortest vector shows that `ν_t²`
is attained.  Every vector of `Dual t` is an integer combination of the rows of the canonical basis
`C`, the row `(2^64, 0, …, 0)` and, for `k = 1, …, t - 1`, the row with `-(a^k mod 2^64)` at
coordinate 0 and 1 at coordinate `k`.  The lower bound then follows from four facts per `t` that
the kernel checks: integer matrices with `U B = C` and `B A = δ I`, a bound `b_i` for each
coordinate with `(ν_t² - 1) ∑_k A_{k i}² < (b_i + 1)² δ²`, and `ν_t² ≤ |z B|²` for each nonzero
`z` with `|z_i| ≤ b_i`, at most 27 vectors.  Cauchy–Schwarz shows that a shorter vector `z B` would
have `|z_i| ≤ b_i`.  [`certificates.py`](certificates.py) computes the certificates from an
LLL-reduced basis `B`, its adjugate `A`, and Fincke–Pohst enumeration, and the theorems do not
depend on it.

| Theorem | Statement |
|---------|-----------|
| `minimalPeriod_affine_iff` | `minimalPeriod (affine a c) x = 2^64 ↔ a % 4 = 1 ∧ c % 2 = 1`, for every `a`, `c`, `x`. |
| `step_minimalPeriod` | From every word, `step` returns after `2^64` steps and not before. |
| `step_bijective` | `step` is a bijection on words. |
| `advance_existsUnique` | For all words `x` and `y`, exactly one count `n : UInt64` gives `advance n x = y`. |
| `advance_ne_self` | `advance n x ≠ x` for every nonzero count `n`. |
| `periodic_testBit_iff`, `step_periodic_testBit_iff` | Bit `k` of the state, for `k < 64`, repeats after `p` steps if and only if `2^(k+1)` divides `p`. |
| `jump_eq` | `jump n x = advance n x`. |
| `advance_topBits` | For `j ≤ 64` and `v < 2^j`, exactly `2^(64 - j)` counts `n` give `(advance n x).toNat / 2^(64 - j) = v`. |
| `dotStates_modEq` | For `s` in `Dual t`, `∑ s_k (step^[k] x).toNat ≡ ∑ s_k (step^[k] 0).toNat (mod 2^64)` for every word `x`. |
| `hyperplanes` | For a nonzero `s` in `Dual t`, a set of at most `∑ \|s_k\|` integers contains `∑ s_k (step^[k] x).toNat` for every word `x`. |
| `hyperplanes_two` to `hyperplanes_six` | The tuples of 2 to 6 successive states lie on at most 4,008,749,872, 2,903,512, 114,468, 12,288, and 2,296 hyperplanes. |
| `spectral_two` to `spectral_six` | Every nonzero vector of `Dual t` has squared length at least `ν_t²`, and `shortest2` to `shortest6` attain it, for `t = 2, …, 6`. |
| `lcg_advance` | The module's bytes decode to the module, whose `advance` export computes `advance` without a trap, and for all words `x` and `y` exactly one count `n` gives `advance n x = y`. |
| `lcg_jump` | The module's bytes decode to the module, whose `jump` export computes `advance` without a trap. |

The proofs use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  Finite checks use
`decide` or `decide +kernel`, which the kernel evaluates without adding an axiom.

## Running it

```sh
tools/leanrun --timeout 60m lake build Verified.Examples.Lcg Examples.Lcg.Spectral
uv run Examples/Lcg/certificates.py
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.Lcg \
  Verified.Examples.Lcg.compiled.module build/verified/lcg.wasm
build/tools/leanexe-wasmtime-host call build/verified/lcg.wasm advance i64 i64:1 i64:0
```

The commands build the proofs, print the certificates of the spectral test, write the module, and
call `advance 1 0` in the Wasmtime host, with the setup of [the repository
README](../../README.md#commands).  The call prints
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
- U. Fincke and M. Pohst, "Improved Methods for Calculating Vectors of Short Length in a Lattice,
  Including a Complexity Analysis," *Mathematics of Computation* 44(170):463–471, 1985,
  [doi:10.1090/S0025-5718-1985-0777278-8](https://doi.org/10.1090/S0025-5718-1985-0777278-8).
- A. K. Lenstra, H. W. Lenstra, Jr., and L. Lovász, "Factoring Polynomials with Rational
  Coefficients," *Mathematische Annalen* 261(4):515–534, 1982,
  [doi:10.1007/BF01457454](https://doi.org/10.1007/BF01457454).
- F. B. Brown, "Random Number Generation with Arbitrary Strides," *Transactions of the American
  Nuclear Society* 71:202–203, 1994, [OSTI 89100](https://www.osti.gov/biblio/89100).
