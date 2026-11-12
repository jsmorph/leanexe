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

[The radius program](#radius-at-a-probability-ce-and-le) uses the same enclosure to return an
interval that contains the circular error at a probability, such as CE90, and one that contains
the linear error, such as LE90, for a normal error with or without a bias.  It compiles into a
module of its own, with soundness and call theorems that state that an accepted interval contains
the unique radius at the probability.

[The adaptive program](#adaptive-panels) returns the same two intervals, for the probability and
the circular error, from panels whose lengths follow the integrand, in a third module with the same
theorems.  For a mean 1,000 standard deviations from the origin, its radius search returns an
interval at most 1 percent of the radius wide at `p = 0.9` from 128 panels, where the search with
equal panels needs 16,384.

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
factor and clamps the lower endpoint at zero.  `expI` and `erfI` call the library's `exp` and
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
| `pc_enclosure` | [Soundness](Soundness.lean) | `pc` returns status 0 | The real values of the inputs satisfy `c11 > 0`, `det C > 0`, and `r > 0`.  The endpoints of the result are finite, and `lo ≤ Model.pc ≤ hi` for those real values. |
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
| `m = (3, 4)`, `σ = (10, 10)`, `r = 10000` | `1.0` | `97.5` | `6.1` | `0.39` |

The width is about 16 times smaller for 16 times as many panels.  The last two rows show the two
weak cases.  For a miss of 50 standard deviations along the second axis, the two error-function
values cancel, and the upper endpoint stays near `2.7e-17`, the rounding of `erf` near ±1 times
the constant factor and the width of `[-r, r]`.  A miss along the first axis keeps its relative
accuracy, as the row before it shows, because the exponential factor carries the small value.
For a disk of 1,000 standard deviations, uniform panels are far wider than the region that holds
the probability, and the upper endpoint exceeds 1.

## Limits of the theorems

The theorems concern the integral of the model, and no theorem concerns the model's four
assumptions.  Hall reports that the two-dimensional value underestimates the probability for
some conjunctions, which indicates a violated assumption.  The realism of the covariance, the
choice of the radius, the agreement of the frames of the mean and the covariance, and the choice
of a threshold are the caller's.

The theorems bound no width.  A wide interval is sound, and its verdict is then 0.  The result's
upper endpoint can exceed 1: `Gaussian.pc_le_one` proves `Model.pc ≤ 1`, but the program does not
clamp the upper endpoint at 1.  The program uses `erf` for both error-function values, so when the two values
cancel, the upper endpoint stays near `7e-16` times the constant factor times `2r`, as the fifth
row of the table shows.  A verdict against a threshold such as `1e-4` is unaffected.

The program takes the encounter-plane quantities.  The projection of two states and two
covariances from a conjunction message onto the encounter plane, the parsing of the message, and
the remediation of a covariance that is not positive definite lie outside this iteration, and
[the review](review.md) lists them as open items.  The theorems rest on the verified compiler's
trusted base, which [the trusted-base document](../../docs/trusted-base.md) describes.

## Radius at a probability: CE and LE

[The radius program](Accuracy.lean) returns an interval that contains the circular error at a
probability `p`: the radius of the disk about the origin that holds, with probability `p`, a
normal error vector in the plane with mean `(m1, m2)`, the bias, and covariance `C`.  It also
returns an interval that contains the linear error, the half-width of the interval about the
origin that holds a normal error on a line with probability `p`.  CE90 and LE90 are the values at
`p = 0.9`, the horizontal and vertical accuracy figures of imagery and elevation products.
[The requirements](requirements.md#radius-at-a-probability-ce-and-le) state the model, the
interface, the method, and the measurements that chose it, and
[the review](review.md#radius-at-a-probability-ce-and-le) records their independent review.
[`verified_compile`](AccuracyVerified.lean) compiles both entries, with `pcWith` and the interval
functions, into a separate module, `accuracy`, of 17,616 bytes, so the module of `pc` and `assess`
and its theorems do not change.

### Interface of the radius program

```text
circularError  m1 m2 c11 c12 c22 p : Float, n k : UInt64  ->  status, lo, hi
linearError    b v p : Float, k : UInt64                     ->  status, lo, hi

m1, m2          mean of the error vector in the plane
c11, c12, c22   covariance of the error vector
b, v            mean and variance of the error on a line
p               probability, strictly between 0 and 1
n               panels of each enclosure of the disk's probability, from 1 to 1,048,576
k               halvings of each bisection, from 0 to 64

status   0   accepted: the radius at p lies in [lo, hi]
         1   rejected input, with zero endpoints
         2   unfinished search, with zero endpoints
```

`circularError` rejects an input when a value is not finite, when `p` is not strictly between 0
and 1, when `c11` or `c22` is not positive, when `n` or `k` lies outside its range, and when the
outward-rounded lower bound of the conditional variance is not positive.  `linearError` rejects an
input when a value is not finite, when `p` is not strictly between 0 and 1, when `v` is not
positive, and when `k` exceeds 64.  Status 2 marks a search that found no radius whose enclosure
of the probability is at least `p`, as happens when `p` lies closer to 1 than the enclosure's
width allows or when an operation overflows at every radius tried.

For the mean `(2, -1)`, the covariance `(25, 6, 16)`, `p = 0.9`, 65,536 panels, and 30 halvings,
`circularError` returns status 0 with `lo = 10.314910589294954` and `hi = 10.316099123899519`.
The reference radius is `10.315504204502986`, and the call takes 7.3 seconds in Wasmtime on one
core of an AArch64 host.  `linearError` with `b = 0`, `v = 1`, `p = 0.9`, and 64 halvings
returns `[1.6448536269514693, 1.6448536269514762]` around the reference `1.6448536269514728`.

### Method of the radius program

For a positive definite covariance, the disk's probability `Model.pc` is zero at radius zero,
continuous, and strictly increasing in the radius, so at most one radius has probability `p`.
The search brackets that radius and then narrows the bracket.  The bracketing starts with the
lower end 0 and the upper end `√(c11 + c22) + √(m1² + m2²)`, and it evaluates `pcWith` at the
upper end at most 16 times.  An evaluation whose lower endpoint is at least `p` ends it.  After
any other evaluation, the upper end becomes the lower end when the evaluation's upper endpoint
lies below `p`, and the upper end then grows by a factor of 1.25.  The radius at any `p` up to
`1 - 2⁻⁵³` is at most 8.6 times the starting radius, and `1.25¹⁶` is about 35.5.  Doubling would
move the evaluation to radii where uniform panels are coarse, and with 64 panels it found no
upper end for a bias of 3 standard deviations.

Two bisections then narrow the bracket from its two sides.  The first evaluates `pcWith` at the
midpoint and moves the lower end there when the result lies below `p`, and the upper end
otherwise, so that its lower end always has a probability shown below `p`.  The second moves the
upper end to a midpoint whose result lies at or above `p`, and the lower end otherwise.  The
result is the lower end of the first and the upper end of the second.  A single bisection would
have to stop at the first midpoint whose enclosure contains `p`, while the two reach the limit
that the enclosure's width sets on each side.  The program integrates over the coordinate of
larger variance: when `c22 > c11` it exchanges `m1` with `m2` and `c11` with `c22` and keeps
`c12`, because
[the measurements](requirements.md#measurements) show the radius interval's relative width then
between `7/n` and `11/n` at `p = 0.9` for every aspect ratio and orientation tried, while with the
other coordinate it grows with the ratio of the standard deviations.

`linearError` runs the same search on an interval evaluation of
`½ [erf((L - b)/κ) + erf((L + b)/κ)]` at the point `L`, with `κ` the interval of `√v · √2`, which
`Model.linearProb_eq` relates to the integral of the density over `[-L, L]`.  The evaluation
needs no panels, so for `p` from 0.5 to 0.99 its interval narrows to 4 to 84 units in the last
place.

### Theorems of the radius program

`Model.RadiusIn P q lo hi` states that `0 ≤ lo ≤ hi`, that exactly one `R ≥ 0` has `P R = q`, and
that this `R` lies in `[lo, hi]`.  Every theorem in the table depends only on the axioms
`propext`, `Classical.choice`, and `Quot.sound`, which
[the axiom audit](../../tests/conjunction/AccuracyAxioms.lean) reports.

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `Model.pc_zero` | [Model](AccuracyModel.lean) | None | `Model.pc` at radius 0 is 0. |
| `Model.pc_swap` | [Model](AccuracyModel.lean) | None | `Model.pc m1 m2 c11 c12 c22 R = Model.pc m2 m1 c22 c12 c11 R`. |
| `Model.pc_strictMonoOn` | [Model](AccuracyModel.lean) | `det C > 0` | `Model.pc` is strictly increasing in `R` on `[0, ∞)`. |
| `Model.pc_continuousOn` | [Model](AccuracyModel.lean) | `c11 > 0`, `det C > 0` | `Model.pc` is continuous in `R` on `[0, ∞)`. |
| `Model.linearProb_eq` | [Model](AccuracyModel.lean) | `v > 0`, `L ≥ 0` | `Model.linearProb b v L = ½ [erf((L - b)/(√v √2)) + erf((L + b)/(√v √2))]`. |
| `Model.linearProb_zero`, `Model.linearProb_strictMonoOn`, `Model.linearProb_continuousOn` | [Model](AccuracyModel.lean) | `v > 0` for the last two | `Model.linearProb` is 0 at 0, and strictly increasing and continuous in `L` on `[0, ∞)`. |
| `Model.radiusIn_of` | [Model](AccuracyModel.lean) | `P` strictly increasing and continuous on `[0, ∞)`, `0 ≤ a`, `0 ≤ c`, `P a < q ≤ P c` | `Model.RadiusIn P q a c`. |
| `circularError_sound` | [Soundness](AccuracySoundness.lean) | `circularError` returns status 0 | The real values satisfy `0 < p < 1`, `c11 > 0`, and `det C > 0`, the endpoints are finite, and `Model.RadiusIn (Model.pc m1 m2 c11 c12 c22) p lo hi` for the real values. |
| `linearError_sound` | [Soundness](AccuracySoundness.lean) | `linearError` returns status 0 | The real values satisfy `0 < p < 1` and `v > 0`, the endpoints are finite, and `Model.RadiusIn (Model.linearProb b v) p lo hi`. |
| `compiled.circularError.implements`, `compiled.linearError.implements` | [Compilation](AccuracyVerified.lean) | Heap with the allocator invariant, a store that holds the table of `exp` at address 4,096, and argument words that represent the arguments | Entries 70 and 71 return words that represent the results, without a trap. |
| `circularError_call`, `linearError_call` | [Call theorems](AccuracyCall.lean) | A ready store | The export returns without a trap the words of the result's `hi`, `lo`, and status, leaves a ready store in which every region of the heap keeps its bytes, and status 0 implies the conclusions of the soundness theorem. |
| `compiled.bytes` | [Compilation](AccuracyVerified.lean) | None | `encode compiled.module` succeeds with bytes that decode to `compiled.module`. |
| `accuracy_file`, `accuracy_file_decode` | [File theorems](AccuracyFile.lean) | `build/verified/accuracy.wasm` as written | The file holds `encode compiled.module` and decodes to `compiled.module`. |

The proofs hold for any enclosure `E` of a probability `P` whose accepted results belong to finite
radii `r ≥ 0` and contain `P r`: `pcWith` is one by `pc_enclosure`, and the linear evaluation is
one by the interval layer's theorems and `Model.linearProb_eq`.  The bracketing keeps a lower end
whose probability lies below `p` and, once it ends, an upper end whose probability is at least
`p`, and each bisection keeps one of the two, by `LeanExe.Dialect.loop_induction`.
`Model.radiusIn_of` then gives the radius by the intermediate value theorem, with uniqueness from
strict monotonicity, so no theorem about the density's total mass is needed.  The strict
monotonicity of `Model.pc` follows from the positive density on a box inside the annulus between
two radii, and its continuity from `Model.pc_eq` and Mathlib's continuity of parametric integrals.
`Model.pc_swap` transfers the result of the exchanged axes, by `integral_prod_swap`.

### Tests of the radius program

`tests/verified/run.sh --cases accuracy` writes the module, validates it, compares
`circularError` and `linearError` with native Lean on [the generated cases](../../tests/TestSupport/Conjunction/AccuracyCases.lean),
runs the axiom audit, and checks the file theorems.  The 237 cases hold the circular inputs at
`p` of 0.9 and 0.99 with 16 and 256 panels and 0 and 20 halvings, the linear inputs with 0, 10,
and 64 halvings, unfinished inputs, and an input for each rejection condition, and the module
agrees with native Lean on every one, bit for bit.

[`tests/conjunction/accuracy.sh`](../../tests/conjunction/accuracy.sh) runs the containment test.
[The reference](../../tests/conjunction/accuracy.py) computes each radius with `mpmath` at 40
digits, independently of the program's method.  The probability of the disk is an integral over
the angle of the radial integral along each ray, which has a closed form in `exp` and `erf`, by
the trapezoid rule on the periodic integrand with points doubled until two values agree to
`1e-24`, and the reference radius is its root.  For a centered isotropic covariance the test also
compares the root with `σ √(-2 ln(1 - p))`, and for a centered linear error with
`√(2v) erfinv(p)`.  The inputs hold 18 means and covariances: isotropic, elongated with either
axis of larger variance, rotated by 10°, 30°, 45°, and 60°, a correlation of 0.99, biases of 1
and 3 standard deviations, and an input with its exchange of axes.  All 292 checks pass: 252
accepted circular results at five probabilities and up to three panel counts contain the
reference, 5 inputs return the required status 2, and 35 linear results contain the
reference.

The test records each interval's width relative to the reference radius.  For the circular
error with 30 halvings, the relative width times `n` lies in the following ranges over the 18
inputs, the same at 256, 4,096, and 65,536 panels to within a few percent, and the test requires
the value at `p = 0.9` to be at most 12.

| `p` | `1e-6` | 0.5 | 0.9 | 0.95 | 0.99 |
|---|---|---|---|---|---|
| Relative width times `n` | 1.3 to 3.0 | 2.1 to 3.8 | 7.2 to 11.0 | 12.9 to 19.7 | 52 to 78 |

The linear intervals are 4 to 84 units in the last place wide for `p` from 0.5 to 0.99 and
about 260 at `p = 1e-6` without a bias.  At `p = 1e-6` with a bias their relative width is
about `1e-9`, because the two error-function values nearly cancel.  The test requires at most
`1e-8`.

### Limits of the radius theorems

The theorems concern the radius of the normal model.  Whether the errors are normal, the realism
of the covariance and the bias, the agreement of their frames, and the choice of `p` are the
caller's.  The theorems bound no width: an accepted interval is sound however wide, and status 2
carries no statement.  The circular error's interval cannot be narrower than about `7/n` to
`11/n` of the radius at `p = 0.9`, and a call costs at most `16 + 2k` evaluations of `pcWith`
with `n` panels each.  The three-dimensional spherical error and covariances known only within
bounds lie outside this iteration.

## Adaptive panels

[The adaptive program](Adaptive.lean) returns an interval that contains the probability of the
disk, as `pc` does, and one that contains the circular error, as `circularError` does, from panels
whose lengths follow the integrand instead of equal panels.  Equal panels spend most of their
number where the integrand is nearly zero when the mean lies many standard deviations from the
origin, and the adaptive panels then give a far narrower interval for the same number of panels
and finish the radius search with far fewer.  For a mean within a few standard deviations of the
origin, equal panels are close to the best partition, and the adaptive panels, which spend part of
the budget on choosing the panels' widths, give intervals up to 16 percent wider and can need more
panels.
[The requirements](requirements.md#adaptive-panels) state the method and the measurements that
chose it, and [the review](review.md#adaptive-panels) records their independent review.
[`verified_compile`](AdaptiveVerified.lean) compiles both entries into a third module, `adaptive`,
of 18,634 bytes, so the modules `conjunction` and `accuracy` and their theorems do not change.

### Interface of the adaptive program

```text
pcAdaptive             m1 m2 c11 c12 c22 r : Float, n : UInt64    ->  status, lo, hi
circularErrorAdaptive  m1 m2 c11 c12 c22 p : Float, n k : UInt64  ->  status, lo, hi

n   most panels of each enclosure of the probability, from 16 to 1,048,576
```

The other arguments and the statuses are those of `pc` and `circularError`.  `pcAdaptive` also
rejects a radius that is not finite, and both entries reject `n` below 16.

For the mean `(100, 0)`, the covariance `(1, 0, 1)`, `p = 0.9`, 4,096 panels, and 30 halvings,
`circularErrorAdaptive` returns status 0 with `lo = 101.28417872452194` and
`hi = 101.28887210144711` around the reference radius `101.28651975739495`, while `circularError`
returns status 0 for that input only from 1,024 panels.  For the mean `(2, -1)`, the covariance
`(25, 6, 16)`, `p = 0.9`, and 65,536 panels, it returns `[10.314844894727734, 10.316163820778275]`
around `10.315504204502986`, an interval 11 percent wider than that of `circularError`.

### Method of the adaptive program

A march covers `[-r, r]` from `-r` with panels whose intervals are the panels of `pc`.  It accepts
a panel whose interval is at most a tolerance `τ` wide and adds the interval to its sum, and it
shortens a panel that is too wide.  Where the integrand is smooth, the width of a panel's interval
falls as the square of the panel's length, so the march multiplies the length of a panel of width
`w` by `min(2, max(1/4, 0.9 √(τ/w)))`, which aims the next panel at a width just below `τ`.  A
march has a number of steps, and its last step accepts the panel from the covered end to `r`
whatever its interval.  `marches` runs three marches, and `pcAdaptive` takes their result.  The
first has the tolerance `r/64` and `n/16` steps.  A panel of width `w` splits into about `√(w/τ)`
panels at the tolerance `τ`, so the second march takes the tolerance at which the first march's
widths predict `n/16` panels, and the third the tolerance at which the second's predict 0.8 times
the panels left, which it takes as its steps.  The result is the part common to the sums of the
second and third marches that covered `[-r, r]` with accepted sums, or the one such sum, times the
constant factor of `pc`, with the lower endpoint clamped at zero.  The common part bounds the width
when the third march runs out of steps and its last panel is wide.  `circularErrorAdaptive` runs
the search of `circularError` with `pcAdaptive` in place of `pc`.

### Theorems of the adaptive program

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and
`Quot.sound`, which [the axiom audit](../../tests/conjunction/AdaptiveAxioms.lean) reports.

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `pcAdaptive_enclosure` | [Soundness](AdaptiveSoundness.lean) | `pcAdaptive` returns status 0 | The real values of the inputs satisfy `c11 > 0`, `det C > 0`, and `r > 0`, `r` is finite, the endpoints are finite, and `lo ≤ Model.pc ≤ hi` for those real values. |
| `circularErrorAdaptive_sound` | [Soundness](AdaptiveSoundness.lean) | `circularErrorAdaptive` returns status 0 | The conclusions of `circularError_sound` for the result of `circularErrorAdaptive`. |
| `guarded_sound` | [Radius soundness](AccuracySoundness.lean) | Every accepted result of a search `S` for a finite probability above 0 holds the radius for its arguments | An accepted result of the input tests of `circularError` around `S` satisfies the conclusions of `circularError_sound`. |
| `marches_used` | [Soundness](AdaptiveSoundness.lean) | None | The three marches of `marches`, which `pcAdaptWith` runs, evaluate at most `n` panels together. |
| `compiled.pcAdaptive.implements`, `compiled.circularErrorAdaptive.implements` | [Compilation](AdaptiveVerified.lean) | Heap with the allocator invariant, a store that holds the table of `exp` at address 4,096, and argument words that represent the arguments | Entries 68 and 69 return words that represent the results, without a trap. |
| `pcAdaptive_call`, `circularErrorAdaptive_call` | [Call theorems](AdaptiveCall.lean) | A ready store | The export returns without a trap the words of the result's `hi`, `lo`, and status, leaves a ready store in which every region of the heap keeps its bytes, and status 0 implies the conclusions of the soundness theorem. |
| `compiled.bytes` | [Compilation](AdaptiveVerified.lean) | None | `encode compiled.module` succeeds with bytes that decode to `compiled.module`. |
| `adaptive_file`, `adaptive_file_decode` | [File theorems](AdaptiveFile.lean) | `build/verified/adaptive.wasm` as written | The file holds `encode compiled.module` and decodes to `compiled.module`. |

One invariant carries a march, `Covers`: the covered part `[-r, t]` lies in `[-r, r]`, a march that
has covered `[-r, r]` ends at `r`, and an accepted sum contains the integral of `Model.core` over
the covered part.  `accept_covers` keeps it when a panel is accepted, by `panel_sound` and the
additivity of the integral, and `marchStep_covers` and `march_covers` through each step and the
loop.  The invariant holds for every tolerance, length, and number of steps, so the tolerances and
lengths that the program computes in binary64 do not enter the proof.  `meet_sound` gives the
common part of two intervals that contain the integral, and `scaled_sound` the constant factor and
`Model.pc_eq`, as in `pc_enclosure`.  `adaptSearch_eq` equates the search with the search of
`AccuracySoundness.lean` over the enclosure `pcAdaptWith`, and `guarded_sound`, which
`circularError_sound` also uses, proves the input tests and the exchange of axes once for both
programs.

### Tests of the adaptive program

`tests/verified/run.sh --cases adaptive` writes the module, validates it, compares `pcAdaptive` and
`circularErrorAdaptive` with native Lean on
[the generated cases](../../tests/TestSupport/Conjunction/AdaptiveCases.lean), runs the axiom
audit, and checks the file theorems.  The 388 cases hold the inputs of the module test of `pc`, an
input with a first variance of `1e-28`, and one whose panels overflow, with 15 to 1,048,577
panels, the inputs of the radius tests and biases of 10, 100, and 1,000 standard deviations at `p`
of 0.9 and 0.99 with 16 and 256 panels, the rejected inputs of the radius program, and unfinished
inputs, and the module agrees with native Lean on every one, bit for bit.

[`tests/conjunction/accuracy.sh`](../../tests/conjunction/accuracy.sh) runs the containment test of
both radius programs, and [the oracle](../../tests/conjunction/accuracy.py) checks each result of
`pcAdaptive` against the polar integral of the containment test of `pc` and each result of
`circularErrorAdaptive` against the reference radius.  All 52 results of `pcAdaptive` on the 13
inputs of the containment test of `pc`, with 16, 100, 256, and 4,096 panels, contain the
reference.  For the disk of 1,000 standard deviations the interval is `1.4e-3` wide at 4,096
panels, against `0.39` with equal panels, and without a bias at 4,096 panels it is 12 percent
narrower than with equal panels.  For a first variance of `1e-28`, which a polar quadrature cannot
resolve, the 4 results contain the probabilities of a strip and a rectangle between which the
probability lies; at 4,096 panels the interval is `[0, 24.8]` around 0.683, a floor that the
panels accepted for their length set.  The 17 inputs that must be rejected, among them one whose
panels overflow and 0, 15, and 1,048,577 panels, return status 1.  All 745 results of
`circularErrorAdaptive` pass: 350 accepted results, the 18 inputs of the radius tests and 7 inputs
with biases of 10 to 1,000 standard deviations at the five probabilities and up to three panel
counts, contain the reference; of 375 results with 32, 64, and 128 panels, 216 contain the
reference and 159 have status 2; 3 unfinished inputs return status 2; and 17 rejected inputs
return status 1.

The test records each radius interval's width relative to the reference radius.  With 30
halvings, the relative width times `n` lies in the following ranges, over 256, 4,096, and 65,536
panels, or 4,096 and 65,536 at `p = 0.99`.  The 18 inputs of the radius tests hold biases of up to
3 standard deviations, and the 7 far inputs biases of 10, 100, and 1,000 standard deviations along
each axis and of 30 standard deviations of the smaller variance of `σ = (10, 1)`.

| Relative width times `n` | `p = 1e-6` | 0.5 | 0.9 | 0.95 | 0.99 |
|---|---|---|---|---|---|
| `circularError`, 18 inputs | 1.3 to 3.0 | 2.1 to 3.8 | 7.2 to 11.0 | 12.8 to 19.7 | 52 to 78 |
| `circularErrorAdaptive`, 18 inputs | 1.1 to 3.0 | 0.61 to 3.2 | 4.9 to 10.7 | 8.7 to 19.5 | 35 to 67 |
| `circularErrorAdaptive`, 7 far inputs | 0.0010 to 0.34 | 0.0038 to 0.82 | 0.018 to 3.0 | 0.038 to 6.2 | 0.19 to 29 |

For the same input and panel count, the adaptive interval's width divided by the interval of
`circularError` has, at 4,096 panels, the median 0.93 and the range 0.55 to 1.16 at `p = 0.9`,
0.45 and 0.25 to 1.06 at 0.5, and 1.09 and 0.60 to 1.14 at 0.99.  The largest ratios belong to
the centered isotropic input, the elongated covariance `σ = (3, 1)`, and the correlated sample, and
the smallest to the bias of 3 standard deviations and the elongated covariance `σ = (1, 100)`.
With 4,096 panels at `p = 0.99`, `circularError` returns status 2 for the biases of 100 and 1,000
standard deviations, so the sweep below compares the two methods on the far inputs.

`tests/conjunction/accuracy.sh --sweep` finds, for each input and probability, the least panel
count of `16, 32, …, 1,048,576` at which each search returns status 0 with 30 halvings, and the
least at which it also returns an interval at most a hundredth of its lower endpoint wide, and it
checks the results there.  Each cell gives the two counts for `circularError`, then for
`circularErrorAdaptive`.

| Input | `p = 1e-6` | 0.5 | 0.9 | 0.95 | 0.99 |
|---|---|---|---|---|---|
| `σ = (1, 1)`, `m = 0` | 16, 256; 16, 128 | 16, 256; 16, 256 | 32, 1,024; 64, 1,024 | 64, 2,048; 128, 2,048 | 512, 8,192; 512, 8,192 |
| `σ = (1, 1)`, `m = (3, 0)` | 16, 256; 16, 256 | 16, 512; 64, 256 | 64, 1,024; 128, 1,024 | 128, 2,048; 128, 1,024 | 1,024, 8,192; 512, 4,096 |
| `σ = (1, 1)`, `m = (0, 3)` | 16, 256; 16, 128 | 16, 256; 32, 256 | 64, 1,024; 64, 1,024 | 128, 2,048; 128, 2,048 | 1,024, 8,192; 512, 4,096 |
| `σ = (1, 1)`, `m = (10, 0)` | 16, 512; 16, 128 | 32, 512; 32, 256 | 128, 1,024; 64, 256 | 256, 2,048; 128, 512 | 2,048, 8,192; 512, 2,048 |
| `σ = (1, 1)`, `m = (0, 10)` | 16, 64; 16, 128 | 32, 256; 32, 256 | 128, 1,024; 128, 512 | 256, 2,048; 128, 1,024 | 2,048, 8,192; 512, 2,048 |
| `σ = (1, 1)`, `m = (100, 0)` | 32, 512; 32, 32 | 256, 512; 32, 128 | 1,024, 2,048; 64, 256 | 2,048, 2,048; 128, 256 | 16,384, 16,384; 512, 512 |
| `σ = (1, 1)`, `m = (0, 100)` | 64, 128; 32, 32 | 256, 256; 32, 128 | 1,024, 2,048; 128, 256 | 2,048, 2,048; 128, 256 | 16,384, 16,384; 512, 512 |
| `σ = (1, 1)`, `m = (1000, 0)` | 512, 512; 32, 32 | 2,048, 2,048; 64, 64 | 16,384, 16,384; 128, 128 | 32,768, 32,768; 128, 256 | 131,072, 131,072; 512, 512 |
| `σ = (1, 1)`, `m = (0, 1000)` | 512, 512; 32, 32 | 2,048, 2,048; 64, 64 | 16,384, 16,384; 128, 128 | 32,768, 32,768; 128, 128 | 131,072, 131,072; 512, 512 |
| `σ = (10, 1)`, `m = (0, 30)` | 16, 32; 16, 64 | 16, 64; 32, 128 | 64, 512; 64, 512 | 128, 1,024; 128, 1,024 | 512, 4,096; 512, 4,096 |
| `C = (25, 6, 16)`, `m = (2, -1)` | 16, 256; 16, 256 | 16, 256; 16, 512 | 32, 1,024; 64, 1,024 | 64, 2,048; 128, 2,048 | 512, 8,192; 512, 8,192 |

At the least count with status 0, the adaptive interval can be several times the radius: with 64
panels for `m = (100, 0)` at `p = 0.9` it is `[100.9, 572.6]` around 101.3, since the lower
endpoint of `pcAdaptive` stays below 0.9 out to a radius of about 600.  The second count compares
useful results.  For a bias of 100 standard deviations or more, the adaptive search reaches a
width of 1 percent with 2 to 256 times fewer panels: 128 against 16,384 at 1,000 standard
deviations and `p = 0.9`, and 512 against 131,072 at 0.99.  For a bias of 10 standard deviations
it needs 2 to 4 times fewer at `p` of 0.9 and above.  Without a bias and for the correlated
sample, equal panels are close to the best partition, and the two searches need the same count at
`p` of 0.9 and above, while at `p` of 0.5 and below the adaptive search needs up to twice as many
for the correlated sample, the elongated input, and the bias of 10 standard deviations along the
second axis.  For the least count with status 0, the adaptive search needs up to four times as
many panels for a bias of up to 3 standard deviations, because its first two marches spend part
of a small budget on the estimate of the tolerance.

### Limits of the adaptive panels

The theorems concern the probability and the radius of the normal model, as those of `pc` and
`circularError` do, and they bound no width.  No theorem concerns the tolerances, so an input on
which the marches place their panels badly gets a wide interval, which is sound, and a panel
accepted for a length below `r · 2⁻⁴⁰` sets a floor on the width.  At the least panel count at
which a search returns status 0, the interval can be wider than the radius.  Without a bias the
integrand varies over most of `[-r, r]`, equal panels are close to the best partition, and the
first two marches spend part of the panels, so the adaptive panels do not narrow the radius
interval at `p` near 1, and at small counts the search can need up to four times as many panels
as with equal panels.  A narrower enclosure there needs a panel enclosure of higher order, such as
the value at the panel's midpoint with a bound on the derivative.

## References

- [Conjunction probability requirements](requirements.md)
- D. T. Hall, Implementation Recommendations and Usage Boundaries for the Two-Dimensional
  Probability of Collision Calculation, AAS 19-632, AAS/AIAA Astrodynamics Specialist Conference,
  2019.  https://ntrs.nasa.gov/citations/20190028900
- NIST Digital Library of Mathematical Functions, section 7.2, Definitions of the error
  functions.  https://dlmf.nist.gov/7.2
