# Conjunction: a proved enclosure of the probability of collision

[The program](Program.lean) computes the two-dimensional probability of collision of two space
objects at a conjunction, the number from which operators decide on avoidance maneuvers.  It
returns an interval `[lo, hi]`, and [the soundness theorem](Soundness.lean) `pc_enclosure` states
that the interval contains the exact value of the model's integral for the real values of the
inputs.  `assess` compares the interval with a threshold, so its verdict of "below" or "above" is
a statement about the model's value.  The program is written in the verified compiler's dialect
on [the interval layer](../../Library/Numerics/Interval/README.md) and takes scalar arguments.

[`verified_compile`](Verified.lean) compiles the program, with the library's `exp` and `erf` and
[the flat encodings](Flat.lean) of its records, into a module of 13,717 bytes.  In Wasmtime,
the module's `pc` and `assess` exports agree with native Lean, bit for bit, on 780 generated
calls.  [The containment test](#tests) finds a reference value of the integral, computed at 50
digits, inside the interval of each of 39 runs.
[The theorems](#theorems) state the enclosure, the meaning of each verdict, the reduction of the
integral to one dimension, and the compilation, and [the limits](#limits-of-the-theorems) state
what they leave out.

## The model

For a short encounter, the standard model takes the relative motion as rectilinear, the position
errors as Gaussian and constant during the encounter, the two objects' errors as independent, and
the objects as spheres, combined into one sphere of radius `r`.  The miss vector then has a
Gaussian distribution in the encounter plane, the plane perpendicular to the relative velocity,
with a mean `m = (m1, m2)` and a covariance `C = [[c11, c12], [c12, c22]]`.  The probability of
collision is the probability that the miss vector lies in the disk of radius `r` about the origin:

`Pc = ∫ over x² + y² ≤ r² of (2π √(det C))⁻¹ exp(-½ (p - m)ᵀ C⁻¹ (p - m)) dp`.

[The model](Model.lean) states this integral as `Model.pc`, over Mathlib's Lebesgue measure on
`ℝ × ℝ`, with the quadratic form written out in the entries of `C`.

## Interface

```text
pc      m1 m2 c11 c12 c22 r : Float, n : UInt64       ->  status, lo, hi
assess  m1 m2 c11 c12 c22 r t : Float, n : UInt64     ->  status, lo, hi, verdict

m1, m2          mean of the miss vector
c11, c12, c22   covariance of the miss vector, c11 > 0
r               combined hard-body radius, r > 0
t               threshold, finite
n               number of panels, from 1 to 1,048,576

status   0   accepted
         1   rejected, with every other field zero
verdict  1   hi < t, so Pc < t
         2   t ≤ lo, so t ≤ Pc
         0   neither
```

Every quantity uses one unit of length, and the covariance uses its square.  The axes of the
encounter plane are any orthonormal pair, the same for the mean and the covariance.  The program
rejects an input when a value is not finite, when `c11` or `r` is not positive, when `n` lies
outside its range, when an interval operation overflows, and when the outward-rounded arithmetic
does not show a positive conditional variance `c22 - c12²/c11`.  The last condition rejects every
covariance that is not positive definite and also one too close to singular.

For the mean `(300, 0)`, the covariance `(10000, 0, 1000000)`, the radius 20, and 4,096 panels,
`pc` returns status 0 with `lo = 2.3100006908943638e-5` and `hi = 2.3122011285882181e-5`.  The
reference value of the integral is `2.3111112e-5`.  `assess` with the threshold `1e-4` returns
the same interval with verdict 1, and `assess_sound` then states that the model's probability is
below `1e-4`.

## Method

The density is the product of the marginal density of the first coordinate and the conditional
density of the second, a Gaussian with mean `μ(x) = m2 + (c12/c11)(x - m1)` and variance
`s² = c22 - c12²/c11`.  For a fixed `x`, the disk holds the second coordinates between
`-h(x)` and `h(x)`, with `h(x) = √(r² - x²)`, and the integral of the conditional density between
them is a difference of two error-function values.  With `k = s √2`,

`Pc = (2 √(2π c11))⁻¹ ∫ from -r to r of exp(-(x - m1)²/(2 c11)) · [erf((h - μ)/k) + erf((h + μ)/k)] dx`.

This form holds for every positive definite covariance and uses no eigenvectors.  `Model.pc_eq`
proves it: `density_factor` factors the density, `disk_integral` writes the integral over the
disk as an iterated integral by Fubini's theorem, and `gauss_window` evaluates the inner integral
with the error function of `LeanExe.ProofKit.RealErf`.

`pcWith` splits `[-r, r]` into `n` panels at the points `-r + 2r (i/n)`, computed in binary64,
with `-r` first and `r` last.  For each panel, `panelCore` evaluates the integrand without its
constant factor in interval arithmetic, with the panel as the interval of `x`:

| Function | Encloses |
|---|---|
| `gaussI` | `exp(-(x - m1)²/(2 c11))`, clamped to `[0, 1]` |
| `chordI` | `√(r² - x²)` |
| `meanI` | `μ(x)` |
| `erfSumI` | `erf((h - μ)/k) + erf((h + μ)/k)`, clamped to `[0, 2]` |

`panel` multiplies the result by an interval that contains the panel's width, `panels` adds the
panels in a loop, and `pcWith` multiplies the sum by an interval that contains the constant
factor and clamps the result to `[0, 1]`, which holds the model's value by `Model.pc_nonneg` and
`Gaussian.pc_le_one`.  `expI` and `erfI` call the library's `exp` and
`erf` at the two ends of an interval and widen each value by two steps, which the functions'
one-step accuracy theorems support.  `setup` computes once the intervals of `2 c11`, `c12/c11`,
`k`, and `r²`.  The width of the result falls in proportion to `1/n`, and no theorem depends on
`n`.

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and
`Quot.sound`, which [the axiom audit](../../tests/conjunction/Axioms.lean) reports.  The real
value of a float is the real number that it represents.
[The verified compiler manual](../../docs/verified-manual.md#the-implements-and-trapfree-theorems)
defines the terms of the generated theorems.

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `Model.pc_eq` | [Model](Model.lean) | `c11 > 0`, `det C > 0`, `r ≥ 0` | `Model.pc` equals `(2 √(2π c11))⁻¹` times the integral of `Model.core` from `-r` to `r`. |
| `Model.pc_nonneg` | [Model](Model.lean) | None | `Model.pc` is not negative. |
| `Gaussian.pc_eq_multivariateGaussian` | [Gaussian](Gaussian.lean) | `c11 > 0`, `det C > 0` | `Model.pc` equals the measure of the disk under Mathlib's `multivariateGaussian` with mean `(m1, m2)` and covariance `C`. |
| `Gaussian.integral_density`, `Gaussian.pc_le_one` | [Gaussian](Gaussian.lean) | `c11 > 0`, `det C > 0` | The density integrates to 1 over the plane, and `Model.pc ≤ 1`. |
| `Model.integral_eq_width_mul` | [Model](Model.lean) | `a ≤ b`, `f` integrable on `[a, b]` with values between `L` and `U` there | The integral of `f` from `a` to `b` is `(b - a) y` for some `y` between `L` and `U`. |
| `pc_enclosure` | [Soundness](Soundness.lean) | `pc` returns status 0 | The real values of the inputs satisfy `c11 > 0`, `det C > 0`, and `r > 0`.  The endpoints of the result are finite, and `lo ≤ Model.pc ≤ hi` for those real values, and `hi ≤ 1`. |
| `assess_sound` | [Soundness](Soundness.lean) | `assess` returns status 0 | `pc` returns status 0 with the same `lo` and `hi`.  Verdict 1 implies `Model.pc < t`, and verdict 2 implies `t ≤ Model.pc`, for the real value of `t`. |
| `compiled.pc.implements`, `compiled.assess.implements` | [Compilation](Verified.lean) | Heap with the allocator invariant, a store that holds the table of `exp` at address 4,096, and argument words that represent the arguments | Entries 54 and 55, the `pc` and `assess` exports, return words that represent `pc` and `assess` of the arguments, without a trap. |
| `compiled.bytes` | [Compilation](Verified.lean) | None | `encode compiled.module` succeeds with bytes that decode to `compiled.module`. |
| `conjunction_file`, `conjunction_file_decode` | [File theorems](File.lean) | `build/verified/conjunction.wasm` as written | The file holds `encode compiled.module` and decodes to `compiled.module`. |

The proof of `pc_enclosure` follows the program.  Each interval function contains the real
function it computes, by the theorems of the interval layer: `gaussI_sound`, `chordI_sound`,
`meanI_sound`, and `erfSumI_sound` give `panelCore_sound`, the inclusion of `Model.core x` for
every `x` of the panel.  `panel_sound` applies `integral_eq_width_mul`, so an accepted panel
contains the integral of `Model.core` over it.  `panels_sound` is an induction on the loop: the
sum of the first `k` panels contains the integral from the first partition point to point `k`.
An accepted division by the interval of `k` gives `k ≠ 0`, hence a positive conditional variance
and a positive determinant, which `Model.pc_eq` requires.

## Tests

`tests/verified/run.sh --cases conjunction` writes the module, validates it, compares `pc` and
`assess` with native Lean on [the generated cases](../../tests/TestSupport/Conjunction/Cases.lean),
runs the axiom audit, and checks the file theorems.  The cases hold 13 valid inputs and 13
rejected ones, each with five panel counts and five thresholds.

[`tests/conjunction/run.sh`](../../tests/conjunction/run.sh) runs the containment test.
[The reference](../../tests/conjunction/reference.py) integrates the density over the disk in
polar coordinates with `mpmath` at 50 digits, independently of the reduction to one dimension,
and requires the value to lie in the interval.  The inputs hold isotropic and elongated
covariances, correlations of ±0.999, radii from `1e-5` to 1,000 standard deviations, a zero miss
vector, and miss distances of 12 and 50 standard deviations.  All 39 runs, 13 inputs at 16, 256,
and 4,096 panels, contain the reference.

In the table, `σ = (σ1, σ2)` stands for the covariance `(σ1², 0, σ2²)`.

| Input | Reference | Width at 16 panels | At 256 | At 4,096 |
|---|---|---|---|---|
| `m = (0, 0)`, `σ = (100, 100)`, `r = 10` | `4.9875e-3` | `7.9e-4` | `5.0e-5` | `3.1e-6` |
| `m = (200, -100)`, `C = (250000, 120000, 90000)`, `r = 15` | `6.3797e-4` | `1.5e-4` | `9.4e-6` | `5.9e-7` |
| `m = (300, 0)`, `σ = (100, 1000)`, `r = 20` | `2.3111e-5` | `5.6e-6` | `3.5e-7` | `2.2e-8` |
| `m = (1200, 0)`, `σ = (100, 100)`, `r = 10` | `3.1958e-34` | `1.1e-34` | `7.1e-36` | `4.4e-37` |
| `m = (0, 5000)`, `σ = (100, 100)`, `r = 10` | `6.57e-545` | `2.7e-17` | `2.7e-17` | `2.7e-17` |
| `m = (3, 4)`, `σ = (10, 10)`, `r = 10000` | `1.0` | `1.0` | `1.0` | `0.19` |

The width is about 16 times smaller for 16 times as many panels.  The last two rows show the two
weak cases.  For a miss of 50 standard deviations along the second axis, the two error-function
values cancel, and the upper endpoint stays near `2.7e-17`, the rounding of `erf` near ±1 times
the constant factor and the width of `[-r, r]`.  A miss along the first axis keeps its relative
accuracy, as the row before it shows, because the exponential factor carries the small value.
For a disk of 1,000 standard deviations, uniform panels are far wider than the region that holds
the probability, and the clamp at 1 sets the upper endpoint.

## Limits of the theorems

The theorems concern the integral of the model, and no theorem concerns the model's four
assumptions.  Hall reports that the two-dimensional value underestimates the probability for
some conjunctions, which indicates a violated assumption.  The realism of the covariance, the
choice of the radius, the agreement of the frames of the mean and the covariance, and the choice
of a threshold are the caller's.

The theorems bound no width.  A wide interval is sound, and its verdict is then 0.  The program
clamps the result to `[0, 1]`, so the upper endpoint is at most 1.  The program uses `erf` for both error-function values, so when the two values
cancel, the upper endpoint stays near `7e-16` times the constant factor times `2r`, as the fifth
row of the table shows.  A verdict against a threshold such as `1e-4` is unaffected.

The program takes the encounter-plane quantities.  The projection of two states and two
covariances from a conjunction message onto the encounter plane, the parsing of the message, and
the remediation of a covariance that is not positive definite lie outside this iteration, and
[the review](review.md) lists them as open items.  The theorems rest on the verified compiler's
trusted base, which [the trusted-base document](../../docs/trusted-base.md) describes.

## References

- [Conjunction probability requirements](requirements.md)
- D. T. Hall, Implementation Recommendations and Usage Boundaries for the Two-Dimensional
  Probability of Collision Calculation, AAS 19-632, AAS/AIAA Astrodynamics Specialist Conference,
  2019.  https://ntrs.nasa.gov/citations/20190028900
- NIST Digital Library of Mathematical Functions, section 7.2, Definitions of the error
  functions.  https://dlmf.nist.gov/7.2
