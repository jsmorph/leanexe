# Conjunction probability requirements

## Purpose and scope

The program computes the two-dimensional probability of collision of two space objects at a
conjunction and returns an interval that contains it, with a verdict against a threshold.  The
first iteration takes the encounter-plane quantities: the mean miss vector, the covariance of the
miss vector, and the combined hard-body radius.  It leaves out the conjunction-message form, which
would project two states and two covariances onto the encounter plane, together with message
parsing, three-dimensional and long-encounter methods, remediation of covariances that are not
positive definite, correlated errors, and non-spherical objects.

## The model

The miss vector has a Gaussian distribution in the encounter plane, the plane perpendicular to the
relative velocity, with mean `m = (m1, m2)` and covariance `C = [[c11, c12], [c12, c22]]`.  The two
objects collide when the miss vector lies in the disk of radius `r` about the origin, so the
probability of collision is

`Pc = ∫ over x² + y² ≤ r² of (2π √(det C))⁻¹ exp(-½ (p - m)ᵀ C⁻¹ (p - m)) dp`.

`Model.pc` states this integral in Lean over Mathlib's Lebesgue measure on `ℝ × ℝ`.  The model
assumes rectilinear relative motion during the encounter, Gaussian position errors that stay
constant during it, independent errors of the two objects, and spherical objects.  No theorem
concerns these assumptions.

## Interface

Every quantity uses one unit of length, such as meters, and the covariance uses its square.  The
two axes of the encounter plane are any orthonormal pair, the same for the mean and the covariance.

| Entry | Arguments | Result |
|---|---|---|
| `pc` | `m1 m2 c11 c12 c22 r : Float`, `n : UInt64` | `Interval`: status, `lo`, `hi` |
| `assess` | `m1 m2 c11 c12 c22 r t : Float`, `n : UInt64` | `Assessment`: status, `lo`, `hi`, verdict |

`n` is the number of panels, from 1 to 1,048,576.  `t` is the threshold.  Status 0 marks an
accepted result and status 1 a rejected one, whose other fields are zero.  The verdict is 1 when
`hi < t`, 2 when `t ≤ lo`, and 0 otherwise.

The program rejects an input when a value is not finite, when `c11` or `r` is not positive, when
`n` lies outside its range, when the computed lower bound of the conditional variance
`c22 - c12²/c11` is negative or the computed scale of the error-function arguments has a lower
bound that is not positive, when an interval operation overflows, and when two successive
partition points are out of order.  A covariance that is not positive definite is therefore
rejected, and so is one too close to singular for the outward-rounded arithmetic to show a
positive conditional variance.

## Method

The density is the product of the marginal density of the first coordinate and the conditional
density of the second, which is Gaussian with mean `μ(x) = m2 + (c12/c11)(x - m1)` and variance
`s² = c22 - c12²/c11`.  The integral over the second coordinate, between the two ends
`±h(x) = ±√(r² - x²)` of the chord, is a difference of error-function values, so

`Pc = (2 √(2π c11))⁻¹ ∫ from -r to r of exp(-(x - m1)²/(2 c11)) · [erf((h - μ)/k) + erf((h + μ)/k)] dx`,

with `k = s √2`.  This form needs no eigenvectors of the covariance.

The program splits `[-r, r]` into `n` panels.  On each panel it evaluates the integrand without
its constant factor in [interval arithmetic](../../Library/Numerics/Interval/README.md), with the
panel as the interval of `x`, and multiplies the result by an interval that contains the panel's
width.  It adds the panels and multiplies the sum by an interval that contains the constant
factor.  The exponential and the error function are the library's, each within one step of the
nearest-even rounding of the real function, and the program widens each computed value by two
steps.  The exponential factor is clamped to `[0, 1]` and the sum of the two error-function values
to `[0, 2]`, bounds that hold for the real functions.  The result is clamped to `[0, 1]`, which
holds the probability.

The partition points are `-r`, `r`, and the points `-r + 2r (i/n)` computed in binary64.  The
program uses a computed point only when it is finite and lies in `[-r, r]`.  The first point is
`-r` and the last is `r`, as doubles.

## Theorems

| Theorem | Statement |
|---|---|
| `Model.pc_eq` | For `c11 > 0`, `det C > 0`, and `r ≥ 0`, `Model.pc` equals the constant factor times the integral of `Model.core` from `-r` to `r`. |
| `pc_enclosure` | When `pc` returns status 0, the real values of the inputs satisfy `c11 > 0`, `det C > 0`, and `r > 0`, the endpoints of the result are finite, and `lo ≤ Model.pc ≤ hi` for those real values, and `hi ≤ 1`. |
| `assess_sound` | When `assess` returns status 0, `pc` returns status 0 with the same `lo` and `hi`.  Verdict 1 implies `Model.pc < t`, and verdict 2 implies `t ≤ Model.pc`. |
| `compiled.pc.implements`, `compiled.assess.implements` | The module's entries return the words of `pc` and `assess` without a trap. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

A containment test compares the interval with a reference value of the integral, computed in
high precision, on inputs that include isotropic and elongated covariances, a correlation near
±1, a radius far smaller and far larger than the standard deviations, a zero miss vector,
probabilities near 1, and probabilities below `1e-30`.  A width test records `hi - lo` against
`n`.  The module test compares the module with native Lean bit for bit on generated inputs.

## What lies outside the theorems

The theorems concern the integral of the model.  The four assumptions of the model, the realism
of the covariance, the choice of the radius, the agreement of the frames of the mean and the
covariance, and the choice of a threshold are the caller's.  The theorems bound no width: a
result with a wide interval is sound, and its verdict is then 0.  The program computes the two
error-function values with `erf`, whose absolute error near ±1 is about `1e-16`, so for a miss
distance of many standard deviations the lower bound falls to zero while the upper bound stays
above the probability by about `1e-16` times the constant factor and the width of `[-r, r]`.

## Radius at a probability: CE and LE

In this section `p` is a probability, `k` the number of halvings of a bisection, and `R0` the
starting radius of a search, unlike the point `p`, the scale `k`, and the conditional standard
deviation `s` of the sections above.

### Purpose and scope

The circular error at probability `p` of a normal error vector in the plane is the radius of the
circle about the origin that holds the vector with probability `p`.  The linear error at
probability `p` of a normal error on a line is the half-width of the interval about the origin
that holds the error with probability `p`.  CE90 and LE90 are the values at `p = 0.9`, the
horizontal and vertical accuracy figures of imagery and elevation products.  For a general normal
distribution the circular error has no closed form, and practice uses approximations.  For any `p`
strictly between 0 and 1 and a centered normal error or one with a bias, the entries
`circularError` and `linearError` either return status 0 with an interval that contains the exact
radius of the model or report that the search did not finish.  The three-dimensional spherical
error, a covariance known only within bounds, and the estimation of a covariance from data lie
outside this iteration.

### Target and cost

Both entries belong to a ground program, a WebAssembly module of the verified compiler beside the
module of `pc`.  They take scalar arguments, return three words, and allocate nothing, so the
module's memory holds only the table of `exp`.  A call of `circularError` evaluates `pcWith` at
most `16 + 2k` times with `n` panels each, at most 144 evaluations of 1,048,576 panels, and each
panel calls `exp` twice and `erf` four times.  A call of `linearError` evaluates the
error-function expression at most `16 + 2k` times, with four calls of `erf` each.  In Wasmtime on one core of an AArch64 host, a call of
`circularError` with 30 halvings took 0.49 seconds with 4,096 panels and 7.3 seconds with
65,536, and a call of `linearError` with 64 halvings 0.03 seconds, each including the start
of the host process.

### The model

For the circular error, the error vector has the normal distribution with mean `m = (m1, m2)`,
the bias, and covariance `C = [[c11, c12], [c12, c22]]`.  Its probability of lying in the disk of
radius `R` about the origin is `Model.pc m1 m2 c11 c12 c22 R`, the integral of the conjunction
model with the bias in place of the miss vector.  For the linear error, the error has the normal
distribution with mean `b` and variance `v`, and its probability of lying in `[-L, L]` is

`Model.linearProb b v L = ∫ over -L ≤ x ≤ L of (2πv)^(-1/2) exp(-(x - b)²/(2v)) dx`,

which equals `½ [erf((L - b)/√(2v)) + erf((L + b)/√(2v))]` for `v > 0` and `L ≥ 0`.

For a positive definite covariance or a positive variance, each probability is zero at radius
zero, continuous, and strictly increasing for radii from zero up, so at most one radius has
probability `p`.  No theorem states that the probability tends to 1 as the radius grows, which
would give such a radius for every `p` below 1.  An accepted result supplies the radius instead:
the program finds a radius whose probability it shows below `p` and one whose probability it shows
at least `p`, and the intermediate value theorem places a radius of probability `p` between them.

### Interface

Every length uses one unit, such as meters, and the covariance and the variance use its square.
The two axes of the plane are any orthonormal pair, the same for the mean and the covariance.

| Entry | Arguments | Result |
|---|---|---|
| `circularError` | `m1 m2 c11 c12 c22 p : Float`, `n k : UInt64` | `Radius`: status, `lo`, `hi` |
| `linearError` | `b v p : Float`, `k : UInt64` | `Radius`: status, `lo`, `hi` |

`n` is the number of panels of each evaluation of the disk probability, from 1 to 1,048,576 as for
`pc`, and `k` is the number of halvings of each bisection, from 0 to 64.  Status 0 marks an
accepted result, whose interval `[lo, hi]` contains the radius at `p`.  Status 1 marks a rejected
input.  Status 2 marks an unfinished search, one that found no radius whose computed probability is
at least `p` within 16 evaluations.  A result with status 1 or 2 has zero endpoints.

`circularError` rejects an input when a value is not finite, when `p` is not strictly between 0
and 1, when `c11` or `c22` is not positive, when `n` lies outside its range, when `k` exceeds 64,
and when the outward-rounded lower bound of the conditional variance `c22 - c12²/c11`, after the
exchange of axes that the method describes, is not positive.  The last condition rejects every
covariance that is not positive definite and also one too close to singular, among them every
covariance with `c11 · c22` below about `5e-324`, since the outward rounding of `c12² = 0` gives
`-5e-324`.  `linearError` rejects an input when a value is not finite, when `p` is not strictly
between 0 and 1, when `v` is not positive, when `k` exceeds 64, and when the outward-rounded lower
bound of `√v · √2` is not positive.

Status 2 follows when the enclosure's width near the radius exceeds about `2(1 - p)`, since no
radius then has an enclosure whose lower endpoint reaches `p`.  The width of `pc`'s enclosure
falls as `1/n` and grows with the ratio of the radius to the largest standard deviation, so `p`
near 1 and a bias of many standard deviations need more panels.  With one or two panels every
panel touches `±R`, where the chord is 0, so the lower endpoint is 0 and every search ends with
status 2.  An input so large that a sum or a square overflows at every radius tried, such as a
covariance of `1e308` or a bias of `1e154`, also ends with status 2.

### Method

`circularError` exchanges the two axes when `c22 > c11`: it exchanges `m1` with `m2` and `c11` with
`c22` and keeps `c12`, so that `pc` integrates over the coordinate of larger variance.  The
probability of the disk does not change under the exchange, and the measurements below show its
effect on the width.  The search starts from the radius `R0 = √(c11 + c22) + √(m1² + m2²)`,
computed in binary64.

The search first brackets the radius.  It starts with the lower end 0, whose probability is zero,
and the upper end `R0`, and it evaluates `pc` at the upper end at most 16 times.  An accepted
evaluation whose lower endpoint is at least `p` ends the bracketing.  After each evaluation that
does not end it, the upper end becomes the lower end when the evaluation is accepted and its upper
endpoint lies below `p`, and the upper end then grows by a factor of 1.25.  A bracketing that ends
without an upper end whose evaluation has a lower endpoint of at least `p` returns status 2.  The
radius at any `p` up to `1 - 2⁻⁵³` is at most `|m| + √λmax · √(2 · 53 ln 2)`, below 8.6 `R0`, so
10 steps of 1.25 pass it and the remaining 6 reach about 4 times it.  Doubling the upper end would
move the evaluation to radii where uniform panels are coarse: with 64 panels and a bias of 3
standard deviations, it found no upper end.

Two bisections then narrow the bracket.  Each halving evaluates `pc` at the midpoint
`(a + c)/2` of the current ends `a` and `c`.  The first bisection moves the lower end to the
midpoint when the evaluation is accepted and its upper endpoint lies below `p`, and moves the upper
end there otherwise, so its lower end always has a probability that `pc` shows below `p`.  The
second moves the upper end to the midpoint when the evaluation is accepted and its lower endpoint
is at least `p`, and moves the lower end there otherwise, so its upper end always has a
probability that `pc` shows at least `p`.  Each bisection runs `k` halvings from the bracket, and
the result is the lower end of the first and the upper end of the second.  Neither the starting
radius nor the midpoints affect soundness, so the program computes them in binary64 without
outward rounding.

`linearError` follows the same steps with `b` and `v` in place of the mean and the covariance, the
starting radius `√v + |b|`, and in place of `pc` an interval evaluation of
`½ [erf((L - b)/κ) + erf((L + b)/κ)]` at the point `L`, with `κ` the interval of `√v · √2`, which
rejects a negative `L`.

### Measurements

A radius whose enclosure contains `p` can be neither a lower nor an upper end, so the radius
interval cannot be much narrower than the width of `pc`'s enclosure near `p` divided by the slope
of the probability in the radius.  The measurement evaluated `pc` at the reference radius for
`p = 0.9`, computed with `mpmath` at 30 digits, and divided the width of the result by the slope
there and by the radius.  In the table, `σ = (σ1, σ2)` stands for the covariance
`(σ1², 0, σ2²)`, and a rotated covariance has eigenvalues 10,000 and 1 with its major axis at the
stated angle from the first axis.  The rows marked "first axis smaller" measure `pc` with the
coordinate of smaller variance as the integration variable, which `circularError` avoids by the
exchange.

| Covariance and mean | Relative width at 256 panels | At 4,096 | At 65,536 |
|---|---|---|---|
| `σ = (1, 1)`, `m = 0` | `2.8e-2` | `1.8e-3` | `1.1e-4` |
| `σ = (1, 3)`, `m = 0`, first axis smaller | `8.0e-2` | `5.0e-3` | |
| `σ = (3, 1)`, `m = 0` | `3.0e-2` | `1.8e-3` | |
| `σ = (1, 10)`, `m = 0`, first axis smaller | `2.7e-1` | `1.7e-2` | |
| `σ = (10, 1)`, `m = 0` | `3.0e-2` | `1.9e-3` | |
| `σ = (1, 100)`, `m = 0`, first axis smaller | `2.7` | `1.7e-1` | |
| `σ = (100, 1)`, `m = 0` | `3.0e-2` | `1.9e-3` | `1.2e-4` |
| Rotated by 45°, `m = 0` | | `2.7e-3` | `1.7e-4` |
| Rotated by 30°, `m = 0` | | `2.2e-3` | `1.4e-4` |
| Rotated by 10°, `m = 0` | | `1.9e-3` | `1.2e-4` |
| `C = (1, 0.9, 1)`, `m = 0` | `4.1e-2` | `2.6e-3` | |
| `σ = (1, 1)`, `m = (1, 0)` | `3.2e-2` | `2.0e-3` | |
| `σ = (1, 1)`, `m = (3, 0)` | `3.5e-2` | `2.2e-3` | |
| `σ = (1, 10)`, `m = (0, 3)`, first axis smaller | `2.8e-1` | `1.8e-2` | |
| `σ = (10, 1)`, `m = (3, 0)` | `3.1e-2` | `2.0e-3` | |
| `C = (25, 6, 16)`, `m = (2, -1)` | `2.9e-2` | `1.8e-3` | |

The relative width falls in proportion to `1/n`.  With the coordinate of larger variance as the
integration variable, it lies between `7/n` and `11/n` for every input of the table, whatever the
ratio of the variances or the orientation of the axes.  With the coordinate of smaller variance,
it grows in proportion to the ratio of the standard deviations, because uniform panels over
`[-R, R]` then spend most of their number where the Gaussian factor of that coordinate is
negligible.  For a result with status 0 at `p = 0.9`, the radius interval is therefore about
`1e-4` of the radius wide at 65,536 panels and about `1e-5` at 1,048,576 panels.  The linear
error needs no panels, and its interval's width is the absolute width of the enclosure of the
error-function expression divided by the slope.  With 64 halvings the containment test measures
4 to 84 units in the last place of the radius for `p` from 0.5 to 0.99, about 260 at `p = 1e-6`
without a bias, and a relative width near `1e-9` at `p = 1e-6` with a bias, where the two
error-function values nearly cancel.

### Theorems

`Model.RadiusIn P q lo hi` states that `0 ≤ lo ≤ hi`, that exactly one `R ≥ 0` has `P R = q`, and
that this `R` lies in `[lo, hi]`.

| Theorem | Statement |
|---|---|
| `Model.pc_swap` | `Model.pc m1 m2 c11 c12 c22 R = Model.pc m2 m1 c22 c12 c11 R`. |
| `Model.pc_zero` | `Model.pc` at radius 0 is 0. |
| `Model.pc_strictMonoOn`, `Model.pc_continuousOn` | For `c11 > 0` and `det C > 0`, `Model.pc` is strictly increasing and continuous in `R` on `[0, ∞)`. |
| `Model.linearProb_eq` | For `v > 0` and `L ≥ 0`, `Model.linearProb b v L` equals the error-function expression of the model. |
| `Model.linearProb_zero`, `Model.linearProb_strictMonoOn`, `Model.linearProb_continuousOn` | For `v > 0`, `Model.linearProb` is 0 at radius 0 and strictly increasing and continuous in `L` on `[0, ∞)`. |
| `Model.radiusIn_of` | A function strictly increasing and continuous on `[0, ∞)`, below `q` at `a ≥ 0` and at least `q` at `c ≥ 0`, satisfies `Model.RadiusIn P q a c`. |
| `circularError_sound` | When `circularError` returns status 0, the real values of the inputs satisfy `0 < p < 1`, `c11 > 0`, and `det C > 0`, the endpoints are finite, and `Model.RadiusIn (Model.pc m1 m2 c11 c12 c22) p lo hi`. |
| `linearError_sound` | When `linearError` returns status 0, the real values satisfy `0 < p < 1` and `v > 0`, the endpoints are finite, and `Model.RadiusIn (Model.linearProb b v) p lo hi`. |
| `compiled.circularError.implements`, `compiled.linearError.implements` | The module's entries return the words of `circularError` and `linearError` without a trap. |
| `circularError_call`, `linearError_call` | A call of the export from a ready store returns the words of the program's result without a trap and leaves a ready store, and a returned status 0 carries the conclusions of the soundness theorem. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

### Tests

A containment test compares each result with a reference radius computed with `mpmath` at 40
digits from the bits of the inputs, independently of the program's method.  For the circular
error, the reference probability is an integral over the angle of the radial integral along each
ray, which has a closed form in `exp` and `erf`, by the trapezoid rule on the periodic integrand
with the points doubled until two values agree to `1e-24`, and the reference radius is its root.
For a centered isotropic error the test also checks the closed form `σ √(-2 ln(1 - p))`, and for a
centered linear error the closed form `√(2v) erfinv(p)`.

The circular inputs hold isotropic and elongated covariances with either axis of larger variance,
covariances rotated by 10°, 30°, 45°, and 60°, a correlation of 0.99, biases of 1 and 3 standard
deviations, and `m = (-1, 2)`, `C = (16, 6, 25)`, the exchange of `m = (2, -1)`,
`C = (25, 6, 16)`, which detects an exchange that negates `c12`.  Each runs with 30 halvings at the
probabilities `1e-6`, 0.5, 0.9, and 0.95 with 256, 4,096, and 65,536 panels, and at 0.99 with
4,096 and 65,536 panels, and each result must have status 0 and contain the reference.  An
accepted circular interval at `p = 0.9` must be at most `12/n` of the reference wide, the bound of
the measurements.  The linear inputs hold the means and variances `(0, 1)`, `(1, 1)`, `(3, 4)`,
`(0.5, 0.25)`, `(-2, 1)`, `(0, 1e-6)`, and `(1000, 1e6)` at the same probabilities with 64
halvings, and each interval must be at most `1e-8` of the reference wide.  The centered isotropic
input must return status 2 at `p = 0.9999999` with 16 panels, at `p = 0.999999` and `p = 0.99`
with 256 panels, and at `p = 0.5` with 1 and 2 panels.

The module test compares the module with native Lean bit for bit on generated inputs.  They hold
the circular inputs at `p` of 0.9 and 0.99 with 16 and 256 panels and 0 and 20 halvings, the
linear inputs at `p` of `1e-6`, 0.9, and 0.99 with 0, 10, and 64 halvings, the unfinished inputs
above, and inputs that each rejection condition rejects: `p` of 0, 1, -0.5, and NaN, a NaN or
infinite mean or covariance entry, `c11` of 0 and -1, `c22` of 0, the covariances `(1, 1, 1)`,
`(1, 2, 1)`, and `(4, 2, 1)`, `n` of 0 and 1,048,577, `k` of 65, and `v` of 0 and -1.

### Samples

The reference radii of the samples come from `mpmath` at 40 digits for the binary64 values of the
inputs.  The results of the circular error are for 65,536 panels and 30 halvings, and those of
the linear error for 64 halvings, all with status 0.

| Entry | Inputs | Reference radius | `lo` | `hi` |
|---|---|---|---|---|
| `circularError` | `m = (0, 0)`, `C = (1, 0, 1)`, `p = 0.9` | `2.1459660262893473` | `2.1458482465022293` | `2.1460839803290779` |
| `circularError` | `m = (3, 0)`, `C = (1, 0, 1)`, `p = 0.9` | `4.4197039765207456` | `4.4194032689304219` | `4.4200061040131047` |
| `circularError` | `m = (0, 0)`, `C = (1, 0, 10000)`, `p = 0.9` | `164.48840265940298` | `164.47972656394398` | `164.49914379142388` |
| `circularError` | `m = (0, 3)`, `C = (1, 0, 100)`, `p = 0.9` | `17.203772037523089` | `17.202728968350613` | `17.204838662401038` |
| `circularError` | `m = (2, -1)`, `C = (25, 6, 16)`, `p = 0.9` | `10.315504204502986` | `10.314910589294954` | `10.316099123899519` |
| `circularError` | `m = (-1, 2)`, `C = (16, 6, 25)`, `p = 0.9` | `10.315504204502986` | `10.314910589294954` | `10.316099123899519` |
| `linearError` | `b = 0`, `v = 1`, `p = 0.9` | `1.6448536269514728` | `1.6448536269514693` | `1.6448536269514762` |
| `linearError` | `b = 1`, `v = 1`, `p = 0.9` | `2.2844680121686751` | `2.2844680121686713` | `2.284468012168679` |
| `linearError` | `b = 3`, `v = 4`, `p = 0.9` | `5.5632088625179976` | `5.56320886251799` | `5.563208862518005` |
| `linearError` | `b = 0`, `v = 1`, `p = 0.5` | `0.67448975019608174` | `0.6744897501960809` | `0.6744897501960829` |
| `linearError` | `b = 0.5`, `v = 0.25`, `p = 0.99` | `1.6633160050017198` | `1.6633160050017093` | `1.663316005001728` |

### What lies outside the theorems

The theorems concern the radius of the normal model.  Whether the errors are normal, the realism
of the covariance and the bias, the agreement of their frames, and the choice of `p` are the
caller's.  The theorems bound no width: an accepted interval is sound however wide, and status 2
carries no statement.  The program reaches no conclusion when `p` lies closer to 1 than the
enclosure's width allows, and for a result with status 0 the interval of the circular error is
about `7/n` to `11/n` of the radius wide at `p = 0.9`.

## Adaptive panels

In this section `L` is the length of a panel, `w` the width of a panel's interval, `τ` a
tolerance on that width, and `R` the radius at which the enclosure is evaluated.

### Purpose and scope

The width of `pcWith`'s interval is about the sum over the panels of `L` times the variation of
the integrand on the panel.  With `n` equal panels that sum is `2R/n` times the total variation of
the integrand over `[-R, R]`.  When the mean lies many standard deviations from the origin, the
radius at a probability is many standard deviations long, while the integrand varies only within a
few standard deviations of the mean, so most equal panels lie where the integrand is almost zero.
The radius search then needs many panels before it finishes: with 30 halvings, `circularError`
returns status 0 at `p = 0.9` from 32 panels without a bias, from 1,024 for a bias of 100 standard
deviations, and from 16,384 for a bias of 1,000.  The entries `pcAdaptive` and
`circularErrorAdaptive` place the panels where the width arises.  For a bias of more than a few
standard deviations, the probability's interval and the radius interval are then far narrower for
the same number of panels, and the search finishes with far fewer.  For a bias of a few standard
deviations or none, the adaptive panels spend part of the budget on the estimate of the tolerance:
the search can need up to four times as many panels as with equal panels at small counts, and at
4,096 panels the enclosure of the probability is up to 16 percent wider.  `linearError` evaluates
no panels, so the linear error lies outside this section.

Where the integrand is smooth, `w` is about `L² g` for a rate `g` that depends on the integrand's
slope on the panel.  A partition into `N` panels of equal `w` then has a total width of about
`(∫ √g)² / N`, against `2R (∫ g) / N` for equal panels.  The Cauchy–Schwarz inequality makes the
first never larger, and it is much smaller when `g` is concentrated in a small part of
`[-R, R]`.  Without a bias the integrand varies over most of `[-R, R]`: for the centered isotropic
input the ratio `(∫ √g)² / (2R ∫ g)`, measured on 65,536 equal panels, is 0.95 at `p = 0.9` and
0.89 at 0.99.  Equal panels are then close to the best partition, and the radius interval's
relative width at `p = 0.99` stays between `35/n` and `67/n` over the inputs of the radius tests.
A panel enclosure of higher order, such as the value at the panel's midpoint with a bound on the
derivative, would change the `1/N` law for every partition; it lies outside this iteration.

The design has no target width: each evaluation spends up to `n` panels.  A target would let an
evaluation far from the radius stop once its interval excludes `p`, but the search cannot know
before an evaluation how narrow an interval decides it, and the evaluations near the radius, which
set the width of the radius interval, need the whole budget.

### Target and cost

Both entries belong to a third ground module, `adaptive`, compiled by the verified compiler, so
that the modules `conjunction` and `accuracy`, their bytes, and their theorems do not change.  The
entries take scalar arguments, return three words, and allocate nothing.  An evaluation of
`pcAdaptive` with `n` panels evaluates at most `n` panels, as the theorem `marches_used` states,
each of which calls `exp` twice and `erf` four times, as a panel of `pc` does, and a call of
`circularErrorAdaptive` evaluates `pcAdaptive` at most `16 + 2k` times.  In Wasmtime on one core of
an AArch64 host, a call with `m = (2, -1)`, `C = (25, 6, 16)`, `p = 0.9`, and 30 halvings took 0.47
seconds with 4,096 panels and 6.6 seconds with 65,536, against 0.52 and 7.35 seconds for
`circularError`, each including the start of the host process.

### Interface

The units and the axes are those of `pc` and `circularError`.

| Entry | Arguments | Result |
|---|---|---|
| `pcAdaptive` | `m1 m2 c11 c12 c22 r : Float`, `n : UInt64` | `Interval`: status, `lo`, `hi` |
| `circularErrorAdaptive` | `m1 m2 c11 c12 c22 p : Float`, `n k : UInt64` | `Radius`: status, `lo`, `hi` |

`n` is the most panels that one enclosure of the probability evaluates, from 16 to 1,048,576, and
`k` the number of halvings of each bisection, from 0 to 64.  The statuses are those of `pc` and of
`circularError`.  `pcAdaptive` rejects an input when `c11` or `r` is not positive, when `r` is not
finite, and when `n` lies outside its range.  It also rejects an input when neither the second nor
the third march covers `[-R, R]` with an accepted sum, and when an operation of the constant factor
overflows.  A value that is not finite, an overflow of an interval operation, and a conditional
variance that the outward-rounded arithmetic does not show positive reject every panel, so they
reject the input.  `circularErrorAdaptive` rejects the inputs that `circularError` rejects, with 16
in place of 1 as the least `n`.

### Method

A march covers `[-R, R]` from `-R` with panels.  It keeps the end `t` of the covered part
`[-R, t]`, an interval that encloses the integral of the integrand over the covered part, the
length `h` of the next panel, which starts at `R/8`, the number of panels evaluated, and the sum of
the square roots of the widths of the accepted panels.  A step evaluates the panel from `t` to `b`,
where `b` is `t + h` when that sum is finite and below `R`, and `R` otherwise, with the interval of
the panels of `pc`.  The step stops the march when the panel's interval is rejected or `b` lies
below `t`.  It accepts the panel when `w ≤ τ` or `b - t ≤ R · 2⁻⁴⁰`, adds the panel's interval to
the sum, and moves `t` to `b`.  After a panel of width `w ≤ τ`, accepted, and after a panel too
wide, rejected, the next length is `h · min(2, max(1/4, 0.9 √(τ/w)))`, computed in that order, or
`2h` when `w` is not positive.  After a panel accepted for its length the next length stays `h`.
A march has a number of steps, and its last step accepts the panel from `t` to `R` whatever its
interval: when that interval is rejected, the march has covered `[-R, R]` with a rejected sum.  A
march of at least one step therefore ends with `[-R, R]` covered or stopped.  The tolerance and the
lengths affect only the width and the number of panels, so the program computes them in binary64
without outward rounding.  A panel accepted for its length sets a floor on the width: for
`m = 0`, `C = (1e-28, 0, 1)`, and `r = 1`, the exponential factor varies on a scale far below
`R · 2⁻⁴⁰`, and the interval of the probability, 0.683, is `[0, 24.8]` at 4,096 panels.

`pcAdaptive` runs three marches on the integrand of `pc`, which the function `marches` returns.
In this paragraph `n/16` and `n/2` are the quotients of `UInt64`.  The first march has the
tolerance `R/64` and `n/16` steps, which covers `[-R, R]` coarsely.  A panel of width `w` at one
tolerance splits into about `√(w/τ)` panels at the tolerance `τ`, so a march at the tolerance
`(S / max(1, K))²`, with `S` the sum of the square roots of the widths of an earlier march's
accepted panels, takes about `K` panels when the earlier march resolved the integrand.  The second
march has that tolerance for `K = n/16` and `n/2` less the first's panels as steps, and the third
has it for `K = 0.8 N`, with `N` the panels left, and `N` steps.  The factor 0.8 leaves room for
the panels that the estimate misses.  When the third march runs out of steps, its last panel covers
the rest of `[-R, R]` and can be wide.  The result is therefore the part common to the sums of the
second and third marches that covered `[-R, R]` with accepted sums, or the one such sum when only
one march did, times the interval of the constant factor of `pc`, with the lower endpoint clamped
at zero.  Each of these sums contains the integral, so their common part does.

`circularErrorAdaptive` is `circularError` with `pcAdaptive` in place of `pc`: the exchange of axes
that makes the first coordinate the one of larger variance, the starting radius, the bracketing,
and the two bisections are those of `circularError`.

### Measurements

The design measurements used models in Python of `pc`'s panel enclosure with the interval layer's
outward rounding.  The table comes from the model of the review, which ports the library's `exp`
and `erf` and reproduces the program's results bit for bit, at the reference radius of probability
`p`.  It compares three enclosures, each with 4,096 panel evaluations: equal panels, one march at
the tolerance that a grid of `log₁₀ τ` from -12 to 0 in steps of 0.25, refined, found narrowest
among those that cover `[-R, R]`, and the three marches of the method.

| Covariance and mean | `p` | Width with equal panels | One march, best tolerance | Three marches |
|---|---|---|---|---|
| `σ = (1, 1)`, `m = 0` | 0.9 | `8.09e-4` | `7.74e-4` | `9.41e-4` |
| `σ = (1, 1)`, `m = 0` | 0.99 | `1.18e-3` | `1.05e-3` | `1.28e-3` |
| `σ = (1, 1)`, `m = (3, 0)` | 0.9 | `1.72e-3` | `7.85e-4` | `9.51e-4` |
| `σ = (1, 1)`, `m = (3, 0)` | 0.99 | `2.12e-3` | `1.05e-3` | `1.27e-3` |
| `σ = (1, 1)`, `m = (0, 3)` | 0.9 | `1.59e-3` | `1.03e-3` | `1.26e-3` |
| `σ = (1, 1)`, `m = (0, 3)` | 0.99 | `2.11e-3` | `1.16e-3` | `1.41e-3` |
| `σ = (1, 1)`, `m = (10, 0)` | 0.9 | `4.41e-3` | `7.32e-4` | `8.87e-4` |
| `σ = (1, 1)`, `m = (10, 0)` | 0.99 | `4.82e-3` | `1.03e-3` | `1.25e-3` |
| `σ = (1, 1)`, `m = (100, 0)` | 0.9 | `3.95e-2` | `6.80e-4` | `8.26e-4` |
| `σ = (1, 1)`, `m = (100, 0)` | 0.99 | `3.99e-2` | `1.01e-3` | `1.22e-3` |
| `σ = (1, 1)`, `m = (0, 100)` | 0.9 | `3.55e-2` | `1.06e-3` | `1.29e-3` |
| `σ = (1, 1)`, `m = (0, 100)` | 0.99 | `3.95e-2` | `1.18e-3` | `1.42e-3` |
| `σ = (1, 1)`, `m = (1000, 0)` | 0.9 | `3.87e-1` | `6.55e-4` | `7.99e-4` |
| `σ = (1, 1)`, `m = (1000, 0)` | 0.99 | `3.89e-1` | `1.00e-3` | `1.23e-3` |
| `σ = (100, 1)`, `m = 0` | 0.9 | `6.41e-4` | `4.57e-4` | `5.55e-4` |
| `σ = (100, 1)`, `m = 0` | 0.99 | `1.00e-3` | `9.07e-4` | `1.11e-3` |
| `C = (25, 6, 16)`, `m = (2, -1)` | 0.9 | `8.13e-4` | `7.52e-4` | `9.11e-4` |
| `C = (25, 6, 16)`, `m = (2, -1)` | 0.99 | `1.16e-3` | `1.04e-3` | `1.25e-3` |

The width of equal panels grows with the bias, in proportion to the radius, while the width of the
best march stays between `6.5e-4` and `1.2e-3` for the isotropic inputs at every bias.  Without a
bias the best march is 4 to 11 percent narrower than equal panels for the centered isotropic
input, and 8 to 29 percent for the elongated and correlated covariances.  The three marches spend 8 to 10 percent of the
panels on the first two marches and leave 10 to 11 percent of the third march's steps unused, and
they are up to 16 percent wider than equal panels.

The statistics that chose the tolerance estimate came from a first model with Python's `exp` and
`erf`, which reproduces `pc`'s sample bit for bit but differs from the program in the last bits on
most results of the marches, while the widths agree to three digits.  It compared the widths at
the radius of probability `p` over 144 configurations: 12 fixed inputs, centered, biased by 3,
100, and 1,000 standard deviations along each axis, elongated with either axis of larger variance,
rotated, and correlated, and 24 random covariances, each at `p` of `1e-6`, 0.5, 0.9, and 0.99.  A
random covariance has the standard deviations `e^u` with `u` uniform on `[-3, 3]` along axes at an
angle uniform on `[0, π)`, and with probability 0.8 a bias of `e^v` times the larger standard
deviation, with `v` uniform on `[-2, 7]`, in a uniform direction, from Python's generator with the
seed 2.  The ratio
of the three marches' width to that of equal panels had the median 0.29 and the maximum 1.17 at
4,096 panels, 0.32 and 1.20 at 1,024, 0.36 and 1.26 at 256, and 0.90 and 2.8 at 128.  The third
march ran out of steps in 36 of the 144 at 256 panels and in none at 1,024 and above, and the
common part with the second march bounded those cases.  Without the common part, the maximum
ratio at 256 panels was 16.5.  The factor 0.9 in place of 0.8 made the third march run out of
steps in 130 of the 144 at 4,096 panels.  On 128 configurations from the seed 1 with 20 random
covariances, a tolerance from the number of an earlier march's panels instead of the sum of the
square roots of their widths left up to 96 percent of the panels unused, with the median ratio
0.44 at 4,096 panels, because the panels that the earlier march lengthened across the tails stay
one panel each at every tolerance.  The review repeated the statistics with its own random set and
the five probabilities and found the maximum ratios 1.163, 1.197, 1.262, and 2.789 at 4,096,
1,024, 256, and 128 panels, the medians 0.245, 0.272, 0.46, and 0.787, and the third march out of
steps in 45 of 144 at 256 panels and in none at 1,024 and above.

The native sweep of the tests gives the least panel count of `16, 32, …, 1,048,576` at which each
search returns status 0, and the least at which it returns an interval at most a hundredth of the
lower endpoint wide, with 30 halvings.  Each cell gives the two counts for `circularError` and then
for `circularErrorAdaptive`.

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

### Theorems

| Theorem | Statement |
|---|---|
| `pcAdaptive_enclosure` | When `pcAdaptive` returns status 0, the real values of the inputs satisfy `c11 > 0`, `det C > 0`, and `r > 0`, `r` is finite, the endpoints of the result are finite, and `lo ≤ Model.pc ≤ hi` for those real values. |
| `circularErrorAdaptive_sound` | When `circularErrorAdaptive` returns status 0, the real values satisfy `0 < p < 1`, `c11 > 0`, and `det C > 0`, the endpoints are finite, and `Model.RadiusIn (Model.pc m1 m2 c11 c12 c22) p lo hi`. |
| `compiled.pcAdaptive.implements`, `compiled.circularErrorAdaptive.implements` | The module's entries return the words of `pcAdaptive` and `circularErrorAdaptive` without a trap. |
| `pcAdaptive_call`, `circularErrorAdaptive_call` | A call of the export from a ready store returns the words of the program's result without a trap and leaves a ready store, and a returned status 0 carries the conclusions of the soundness theorem. |
| `marches_used` | The three marches of `marches`, which `pcAdaptWith` runs, evaluate at most `n` panels together. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  No
theorem concerns the tolerances or the lengths.

### Tests

The containment test checks `pcAdaptive` on the 13 inputs of the containment test of `pc` with 16,
100, 256, and 4,096 panels against the polar integral of that test, and each result must have
status 0 and contain it.  For `m = 0`, `C = (1e-28, 0, 1)`, and `r = 1`, which a polar quadrature
cannot resolve, the interval must contain both the probability of the strip `|y| ≤ r` and that of
the rectangle `|x| ≤ 100 √c11`, `|y| ≤ √(r² - 100² c11)`, between which the probability lies.  The
rejected inputs of the module test of `pc`, the input `m = (-1.3e154, 0)`,
`C = (2e307, 0, 2e307)`, `r = 1.3e154`, whose panels overflow, and 0, 15, and 1,048,577 panels
must return status 1.

It checks `circularErrorAdaptive` on the 18 inputs of the radius tests and on biases of 10, 100,
and 1,000 standard deviations along each axis and of 30 standard deviations of the smaller
variance of `σ = (10, 1)`, with 30 halvings, at the probabilities `1e-6`, 0.5, 0.9, and 0.95 with
256, 4,096, and 65,536 panels and at 0.99 with 4,096 and 65,536 panels.  Each result must have
status 0 and contain the reference radius, and an accepted interval at `p = 0.9` must be at most
`14/n` of the reference wide.  With 32, 64, and 128 panels at the five probabilities, a result may
have status 2 and otherwise must contain the reference.  The centered isotropic input must return
status 2 at `p = 0.9999999` with 256 panels, at `p = 0.999999` with 1,024, and at `p = 0.99` with
16, and the rejected inputs of the radius program, with 64 panels in place of 16, and an input with
15 panels must return status 1.

A sweep finds, for the centered isotropic input, biases of 3 standard deviations along each axis,
the far inputs above, and `m = (2, -1)`, `C = (25, 6, 16)`, at each of the five probabilities, the
least panel count of `16, 32, …, 1,048,576` at which each of `circularError` and
`circularErrorAdaptive` returns status 0, and the least at which it also returns an interval at
most a hundredth of its lower endpoint wide, and the test checks the results at those counts.

The module test compares the module with native Lean bit for bit on generated inputs: `pcAdaptive`
on the valid and rejected inputs of the module test of `pc`, the thin input and the overflowing
input above, with 15, 16, 64, 100, 256, and 1,048,577 panels, `circularErrorAdaptive` on the
inputs of the radius tests and the far inputs at `p` of 0.9 and 0.99 with 16 and 256 panels and 0
and 20 halvings, the rejected inputs of the radius program with 64 panels in place of 16, an input
with 15 panels, and the unfinished inputs above.

### Samples

The reference values come from `mpmath` for the binary64 values of the inputs: the polar integral
of the containment test of `pc` for the probability, at 50 digits, and the radius of the radius
tests, at 40 digits.  Every result has status 0, and the radius results are for 30 halvings.

| Entry | Inputs | `n` | Reference | `lo` | `hi` |
|---|---|---|---|---|---|
| `pcAdaptive` | `m = (300, 0)`, `C = (10000, 0, 1000000)`, `r = 20` | 4,096 | `2.311111184070202e-5` | `2.3099828652149567e-5` | `2.3122382137762846e-5` |
| `circularErrorAdaptive` | `m = (0, 0)`, `C = (1, 0, 1)`, `p = 0.9` | 4,096 | `2.1459660262893473` | `2.1437827833914893` | `2.148166650384631` |
| `circularErrorAdaptive` | `m = (0, 0)`, `C = (1, 0, 1)`, `p = 0.99` | 4,096 | `3.0348542587702924` | `3.014414534122672` | `3.0566889775613184` |
| `circularErrorAdaptive` | `m = (3, 0)`, `C = (1, 0, 1)`, `p = 0.9` | 4,096 | `4.4197039765207456` | `4.417046792707405` | `4.422376504385298` |
| `circularErrorAdaptive` | `m = (2, -1)`, `C = (25, 6, 16)`, `p = 0.9` | 65,536 | `10.315504204502986` | `10.314844894727734` | `10.316163820778275` |
| `circularErrorAdaptive` | `m = (100, 0)`, `C = (1, 0, 1)`, `p = 0.9` | 4,096 | `101.28651975739495` | `101.28417872452194` | `101.28887210144711` |
| `circularErrorAdaptive` | `m = (0, 1000)`, `C = (1, 0, 1)`, `p = 0.9` | 4,096 | `1001.2820512453886` | `1001.2784296211054` | `1001.2856911535264` |
| `circularErrorAdaptive` | `m = (1000, 0)`, `C = (1, 0, 1)`, `p = 0.99` | 4,096 | `1002.3268472933128` | `1002.30458296537` | `1002.3505982405738` |

### What lies outside the theorems

The theorems concern the probability and the radius of the normal model, as those of `pc` and
`circularError` do, and they bound no width.  The width and the number of panels depend on the
tolerances, which no theorem concerns: an input on which the marches place their panels badly
gets a wide interval, which is sound.  At the least panel count at which a search returns status
0, the interval can be wider than the radius.  For `p` near 1 without a bias the adaptive panels
narrow the radius interval little, since equal panels are there close to the best partition.
