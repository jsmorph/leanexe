# Pseudorandom generators with proofs

## Scope

These files define textbook pseudorandom number generators as LeanExe programs and prove their
periods and structure as Lean theorems.  The programs use only `UInt64` words, wrapping arithmetic,
and `LeanExe.loop`, so the theorems describe the values that a compiled module returns once the
programs pass through `verified_compile`.  The files import no `Verified.*` module, and no generator
is compiled yet.  Every theorem depends only on the axioms `propext`, `Classical.choice`, and
`Quot.sound`.  No proof uses `native_decide`: finite checks use `decide`, or `decide +kernel`, which
the kernel evaluates without adding an axiom.

| Generator | File | Proved | Planned |
|-----------|------|--------|---------|
| LCG modulo `2^64` | [The LCG](Lcg.lean) | Hull–Dobell conditions, bijectivity, each word once per period, bit periods | jump-ahead, output functions |
| Park–Miller | `ParkMiller.lean` | none | primality of `2^31 - 1`, period `2^31 - 2` |
| xorshift64 | `Xorshift.lean` | none | zero stays zero and nonzero stays nonzero, period `2^64 - 1` |

## Linear congruential generator modulo 2^64

`affine a c x` is `a * x + c` modulo `2^64`, `step` is
`affine 6364136223846793005 1442695040888963407`, and `advance n x` applies `step` `n` times with
`LeanExe.loop`.  The multiplier is the one that the MMIX Supplement's `rsixfour.c` attributes to
Knuth, *The Art of Computer Programming*, Volume 2, Section 3.3.4, page 108.  The increment is
`PCG_DEFAULT_INCREMENT_64` of O'Neill's PCG library, which pairs it with the same multiplier, and
secondary sources call the pair Knuth's MMIX generator.  `rsixfour.c` itself uses the increment
`9754186451795953191`.  Hull and Dobell's theorem, Theorem A of Knuth's Section 3.2.1.2, states that
an LCG modulo `m` has period `m` if and only if `c` is prime to `m`, `a - 1` is divisible by every
prime factor of `m`, and `a - 1` is divisible by 4 when `m` is.  For `m = 2^64` the conditions are
`c % 2 = 1` and `a % 4 = 1`.

The proof of sufficiency computes the iterates of `affine a c` by squaring.  `2^k` steps form the
affine map with coefficients `doubled a c k`, where squaring takes `(b, d)` to
`(b * b, (b + 1) * d)`.  Under the conditions, induction with `ring` shows `b = 1 + 2^(k+2) * t` and
`d = 2^k * (2 * s + 1)` for some words `t` and `s`.  At `k = 64` the map is the identity, and at
`k = 63` it adds `2^63`, so Mathlib's `minimalPeriod_eq_prime_pow` gives the minimal period `2^64`
at every word.  For necessity, reduction modulo 4 is a ring homomorphism from words to `ZMod 4`, and
a point of period `2^64` reaches every word, so the reduced affine map reaches every residue.
`decide` checks all 64 choices of coefficients and start in `ZMod 4`: when the coefficients fail the
conditions, the orbit stays among its first four iterates and misses a residue.  For the bits, `2^k`
steps add `2^k` plus a multiple of `2^(k+1)`, which complements bit `k`, and the 2-adic valuation of
a candidate period finishes the argument.

| Theorem | Statement |
|---------|-----------|
| `minimalPeriod_affine_iff` | `minimalPeriod (affine a c) x = 2^64 ↔ a % 4 = 1 ∧ c % 2 = 1`, for every `a`, `c`, `x`. |
| `step_minimalPeriod` | From every word, `step` returns after `2^64` steps and not before. |
| `step_bijective` | `step` is a bijection on words. |
| `advance_existsUnique` | For all words `x` and `y`, exactly one count `n : UInt64` gives `advance n x = y`. |
| `advance_ne_self` | `advance n x ≠ x` for every nonzero count `n`. |
| `periodic_testBit_iff`, `step_periodic_testBit_iff` | Bit `k` of the state, for `k < 64`, repeats after `p` steps if and only if `2^(k+1)` divides `p`. |

The bit theorem states the generator's known weakness exactly: bit 0 alternates, and only bit 63 has
the full period.  A jump-ahead function, which computes `advance n x` with 64 squarings instead of
`n` steps as Brown describes, follows from `doubled` and needs a loop invariant over the bits of
`n`.  Output functions that keep the high bits inherit an exact equidistribution from
`advance_existsUnique`: over one period, each value of the top `j` bits occurs `2^(64-j)` times.
Both are of low difficulty.

## Park–Miller minimal standard generator

The step is `16807 * x % 2147483647` on words, with the state in `[1, 2^31 - 2]`.  Park and Miller
proposed it as a minimal standard in 1988, after Lewis, Goodman, and Miller.  In 64-bit arithmetic
the product is below `2^46`, so the program computes the product and the remainder directly.  Park
and Miller give Schrage's method for 32-bit arithmetic, which a later theorem may prove equal to the
direct computation.

The modulus `p = 2^31 - 1` is prime, and `p - 1 = 2 · 3^2 · 7 · 11 · 31 · 151 · 331`.  Mathlib's
`lucas_primality` proves the primality of `p` from a witness `a` with `a^(p-1) = 1` and
`a^((p-1)/q) ≠ 1` for each prime `q` dividing `p - 1`.  The same seven inequalities and
`orderOf_eq_of_pow_and_pow_div_prime` give 16807 the order `p - 1` in `ZMod p`, so 16807 is a
primitive root.  `norm_num`'s `PowMod` extension evaluates each `a^e % p` by repeated squaring with
a proof, so no step multiplies `2^31` times.  For `x` in `[1, p - 1]`, `n` steps give
`16807^n * x % p`, so the minimal period is `p - 1 = 2^31 - 2` and each value in the range occurs
once per period.  The difficulty is low to moderate, mostly in moving between words, natural
numbers, and `ZMod p`.

## Marsaglia's xorshift64

The step is `x ^= x << 13; x ^= x >> 7; x ^= x << 17`, the 64-bit example of Marsaglia's paper,
whose triple `(13, 7, 17)` is among his 275 triples for which the matrix `T` of the step has order
`2^64 - 1` among nonsingular 64 × 64 matrices over GF(2).  The step distributes over xor and maps 0
to 0.  Each of its three xorshifts is injective, since `d = d <<< a` or `d = d >>> a` with `a > 0`
forces every bit of `d` to 0 by induction on the bit position.  The step is then a bijection, and a
nonzero state never becomes 0.  These properties are of low difficulty.

The period `2^64 - 1` from every nonzero state is harder.  Marsaglia's proof of his criterion uses
the characteristic polynomial of `T`, and a formal version needs polynomials over GF(2) and
Cayley–Hamilton, which Mathlib has, with a large amount of connecting work.  A proof about one orbit
avoids that theory.  If the state 1 has minimal period `N = 2^64 - 1`, its orbit holds `N` distinct
nonzero words, which are all of them, so every nonzero word lies on the orbit and has the same
minimal period.  The period of 1 follows from `step^[N] 1 = 1` and `step^[N/q] 1 ≠ 1` for the seven
primes `q` of `2^64 - 1 = 3 · 5 · 17 · 257 · 641 · 65537 · 6700417`.  These iterates need
jump-ahead: the matrix of the step as 64 column words, 64 squarings, and a product for each of the
eight exponents, a few hundred thousand word operations for the kernel.  The proof that the matrix
arithmetic computes the iterates is short, since the step is linear over xor.  The kernel's time for
the computation is unknown and needs a prototype before the approach is chosen.

## Later candidates

SplitMix64, in [the SplitMix64 example](../../Examples/Prng/README.md), advances a Weyl sequence,
which is the case `a = 1` of the LCG theorems, and its output mixer is a bijection because xorshifts
and multiplication by an odd constant are.  PCG combines an LCG state with an output permutation and
has the LCG's period.  xoshiro256** has period `2^256 - 1`, which requires the primitivity of a
degree-256 polynomial over GF(2), a hard proof.  Statistical properties beyond periods and exact
equidistribution, such as the spectral test of an LCG, need lattice theory and are not planned.

## Decisions for the user

1. The LCG increment: `1442695040888963407`, PCG's default and the one in `step`, or
   `9754186451795953191`, the one in `rsixfour.c`.  Both satisfy the conditions, so the theorems
   hold for either.
2. The Park–Miller program: direct 64-bit arithmetic or Schrage's 32-bit method, and the treatment
   of seeds outside `[1, 2^31 - 2]`, since 0 is a fixed point.
3. The location of the programs: in these files, or in `Examples/<Name>/Program.lean` with a
   `Verified/Examples` file for the compilation, as the drone planner has.
4. The xorshift period: the orbit computation above, after a prototype measures the kernel's time,
   or a formal version of Marsaglia's polynomial argument.
5. The statistical properties worth proving beyond periods and equidistribution.

## Compiling

Once `Verified/` settles, each file gains an import of `Verified.Reflect.Command` and a command such
as `verified_compile compiled := [affine, step, advance]`.  A theorem then combines
`compiled.advance.implements` with `advance_existsUnique`, as `drone_compute` combines the
compiler's theorem with the planner's own.  The programs use calls, word constants, arithmetic, and
`LeanExe.loop` with an unused index, all of which the reflector accepts.  `Verified.lean` must also
import the new modules for `lake build Verified` to check them.

## Plan

- [x] Research the generators, sources, and proof methods (2026-10-09).
- [x] LCG: Hull–Dobell conditions for `2^64` in both directions, bijectivity, each word once per
  period, bit periods (2026-10-09).
- [ ] LCG: jump-ahead and high-bit equidistribution.
- [ ] Park–Miller: primality, primitive root, period, each value once per period.
- [ ] xorshift64: linearity, injectivity, zero and nonzero states.
- [ ] xorshift64: prototype the kernel computation of `step^[N] 1`, then the period.
- [ ] `verified_compile` for each generator.

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
- F. B. Brown, "Random Number Generation with Arbitrary Strides," *Transactions of the American
  Nuclear Society* 71:202–203, 1994, [OSTI 89100](https://www.osti.gov/biblio/89100).
- P. A. W. Lewis, A. S. Goodman, and J. M. Miller, "A Pseudo-Random Number Generator for the
  System/360," *IBM Systems Journal* 8(2):136–146, 1969,
  [doi:10.1147/sj.82.0136](https://doi.org/10.1147/sj.82.0136).
- S. K. Park and K. W. Miller, "Random Number Generators: Good Ones Are Hard to Find,"
  *Communications of the ACM* 31(10):1192–1201, 1988,
  [doi:10.1145/63039.63042](https://doi.org/10.1145/63039.63042).
- L. Schrage, "A More Portable Fortran Random Number Generator," *ACM Transactions on Mathematical
  Software* 5(2):132–138, 1979, [doi:10.1145/355826.355828](https://doi.org/10.1145/355826.355828).
- G. Marsaglia, "Xorshift RNGs," *Journal of Statistical Software* 8(14), 2003,
  [doi:10.18637/jss.v008.i14](https://doi.org/10.18637/jss.v008.i14).
