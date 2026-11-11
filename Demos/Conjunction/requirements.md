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
to `[0, 2]`, bounds that hold for the real functions.

The partition points are `-r`, `r`, and the points `-r + 2r (i/n)` computed in binary64.  The
program uses a computed point only when it is finite and lies in `[-r, r]`.  The first point is
`-r` and the last is `r`, as doubles.

## Theorems

| Theorem | Statement |
|---|---|
| `Model.pc_eq` | For `c11 > 0`, `det C > 0`, and `r ≥ 0`, `Model.pc` equals the constant factor times the integral of `Model.core` from `-r` to `r`. |
| `pc_enclosure` | When `pc` returns status 0, the real values of the inputs satisfy `c11 > 0`, `det C > 0`, and `r > 0`, the endpoints of the result are finite, and `lo ≤ Model.pc ≤ hi` for those real values. |
| `assess_sound` | When `assess` returns status 0, `pc` returns status 0 with the same `lo` and `hi`.  Verdict 1 implies `Model.pc < t`, and verdict 2 implies `t ≤ Model.pc`. |
| `compiled.pc.implements`, `compiled.assess.implements` | The module's entries return the words of `pc` and `assess`, or trap at `unreachable`. |

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

### Purpose and scope

The circular error at probability `p` of a normal error vector in the plane is the radius of the
circle about the origin that holds the vector with probability `p`.  The linear error at
probability `p` of a normal error on a line is the half-width of the interval about the origin
that holds the error with probability `p`.  CE90 and LE90 are the values at `p = 0.9`, the
horizontal and vertical accuracy figures of imagery and elevation products.  For a general normal
distribution the circular error has no closed form, and practice uses approximations.  The entries
`circularError` and `linearError` return an interval that contains the exact radius of the model
for any `p` strictly between 0 and 1, for a centered normal error or one with a bias.  The
three-dimensional spherical error, a covariance known only within bounds, and the estimation of a
covariance from data lie outside this iteration.

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
at least `p` within its doublings, as happens when `p` lies closer to 1 than the enclosure's width.
A result with status 1 or 2 has zero endpoints.

`circularError` rejects an input when a value is not finite, when `p` is not strictly between 0
and 1, when `c11` or `c22` is not positive, when `n` lies outside its range, when `k` exceeds 64,
and when the outward-rounded lower bound of the conditional variance `c22 - c12²/c11`, after the
exchange of axes that the method describes, is not positive.  The last condition rejects every
covariance that is not positive definite and also one too close to singular.  `linearError`
rejects an input when a value is not finite, when `p` is not strictly between 0 and 1, when `v`
is not positive, when `k` exceeds 64, and when the outward-rounded lower bound of `√v · √2` is not
positive.

### Method

`circularError` exchanges the two axes when `c22 > c11`, which exchanges `m1` with `m2` and `c11`
with `c22`, so that `pc` integrates over the coordinate of larger variance.  The probability of
the disk does not change under the exchange, and the measurements below show its effect on the
width.  The search starts from the radius `s = √(c11 + c22) + √(m1² + m2²)`, computed in binary64.

The search first brackets the radius.  It starts with the lower end 0, whose probability is zero,
and the upper end `s`, and it evaluates `pc` at the upper end at most 16 times.  An accepted
evaluation whose lower endpoint is at least `p` ends the bracketing.  Otherwise an accepted
evaluation whose upper endpoint lies below `p` moves the lower end to the upper end, and in every
case but the first the upper end doubles.  A bracketing that ends without an upper end whose
evaluation has a lower endpoint of at least `p` returns status 2.

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
`½ [erf((L - b)/κ) + erf((L + b)/κ)]` at the point `L`, with `κ` the interval of `√v · √2`.  A
call of `circularError` evaluates `pc` at most `16 + 2k` times with `n` panels each, and a call of
`linearError` evaluates the error-function expression at most `16 + 2k` times.

### Measurements

A radius whose enclosure contains `p` can be neither a lower nor an upper end, so the radius
interval cannot be much narrower than the width of `pc`'s enclosure near `p` divided by the slope
of the probability in the radius.  The measurement evaluated `pc` at the reference radius for
`p = 0.9`, computed with `mpmath` at 30 digits, and divided the width of the result by the slope
there and by the radius.  In the table, `σ = (σ1, σ2)` stands for the covariance
`(σ1², 0, σ2²)`, and a rotated covariance has eigenvalues 10,000 and 1 with its major axis at the
stated angle from the first axis.

| Covariance and mean | Relative width at 256 panels | At 4,096 | At 65,536 |
|---|---|---|---|
| `σ = (1, 1)`, `m = 0` | `2.8e-2` | `1.8e-3` | `1.1e-4` |
| `σ = (1, 3)`, `m = 0` | `8.0e-2` | `5.0e-3` | |
| `σ = (3, 1)`, `m = 0` | `3.0e-2` | `1.8e-3` | |
| `σ = (1, 10)`, `m = 0` | `2.7e-1` | `1.7e-2` | |
| `σ = (10, 1)`, `m = 0` | `3.0e-2` | `1.9e-3` | |
| `σ = (1, 100)`, `m = 0` | `2.7` | `1.7e-1` | |
| `σ = (100, 1)`, `m = 0` | `3.0e-2` | `1.9e-3` | `1.2e-4` |
| Rotated by 45°, `m = 0` | | `2.7e-3` | `1.7e-4` |
| Rotated by 30°, `m = 0` | | `2.2e-3` | `1.4e-4` |
| Rotated by 10°, `m = 0` | | `1.9e-3` | `1.2e-4` |
| `C = (1, 0.9, 1)`, `m = 0` | `4.1e-2` | `2.6e-3` | |
| `σ = (1, 1)`, `m = (1, 0)` | `3.2e-2` | `2.0e-3` | |
| `σ = (1, 1)`, `m = (3, 0)` | `3.5e-2` | `2.2e-3` | |
| `σ = (1, 10)`, `m = (0, 3)` | `2.8e-1` | `1.8e-2` | |
| `σ = (10, 1)`, `m = (3, 0)` | `3.1e-2` | `2.0e-3` | |
| `C = (25, 6, 16)`, `m = (2, -1)` | `2.9e-2` | `1.8e-3` | |

The relative width falls in proportion to `1/n`.  With the coordinate of larger variance as the
integration variable, it lies between `7/n` and `11/n` for every input of the table, whatever the
ratio of the variances or the orientation of the axes.  With the coordinate of smaller variance,
it grows in proportion to the ratio of the standard deviations, because uniform panels over
`[-R, R]` then spend most of their number where the Gaussian factor of that coordinate is
negligible.  At 65,536 panels the radius interval is therefore about `1e-4` of the radius wide,
and at 1,048,576 panels about `1e-5`.  The linear error needs no panels, and its interval should
narrow to a few units in the last place of the radius.

### Theorems

| Theorem | Statement |
|---|---|
| `Model.pc_swap` | `Model.pc m1 m2 c11 c12 c22 R = Model.pc m2 m1 c22 c12 c11 R`. |
| `Model.pc_zero` | `Model.pc` at radius 0 is 0. |
| `Model.pc_strictMonoOn`, `Model.pc_continuousOn` | For `c11 > 0` and `det C > 0`, `Model.pc` is strictly increasing and continuous in `R` on `[0, ∞)`. |
| `Model.linearProb_eq` | For `v > 0` and `L ≥ 0`, `Model.linearProb b v L` equals the error-function expression of the model. |
| `Model.linearProb_zero`, `Model.linearProb_strictMonoOn`, `Model.linearProb_continuousOn` | For `v > 0`, `Model.linearProb` is 0 at radius 0 and strictly increasing and continuous in `L` on `[0, ∞)`. |
| `circularError_sound` | When `circularError` returns status 0, the real values of the inputs satisfy `0 < p < 1`, `c11 > 0`, and `det C > 0`, the endpoints are finite with `0 ≤ lo ≤ hi`, exactly one `R ≥ 0` has `Model.pc m1 m2 c11 c12 c22 R = p`, and `lo ≤ R ≤ hi`. |
| `linearError_sound` | When `linearError` returns status 0, the real values satisfy `0 < p < 1` and `v > 0`, the endpoints are finite with `0 ≤ lo ≤ hi`, exactly one `L ≥ 0` has `Model.linearProb b v L = p`, and `lo ≤ L ≤ hi`. |
| `compiled.circularError.implements`, `compiled.linearError.implements` | The module's entries return the words of `circularError` and `linearError` without a trap. |
| `circularError_call`, `linearError_call` | A call of the export from a ready store returns the words of the program's result without a trap and leaves a ready store, and a returned status 0 carries the conclusions of the soundness theorem. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

### Tests

A containment test compares each accepted interval with a reference radius computed with `mpmath`
at 30 digits or more, independently of the program's method.  For the circular error, the
reference probability is an integral over the angle of the radial integral along each ray, which
has a closed form in `exp` and `erf`, by the trapezoid rule on the periodic integrand, checked
against the rule with twice the points, and the reference radius is its root.  For a centered
isotropic error the test also checks the closed form `σ √(-2 ln(1 - p))`, and for a centered
linear error the closed form `√(2v) erfinv(p)`.  The inputs hold isotropic and elongated
covariances with either axis of larger variance, rotated covariances, a correlation near 1,
biases of 1 and 3 standard deviations, the probabilities `1e-6`, 0.5, 0.9, 0.95, and 0.99, and
panel counts of 256, 4,096, and 65,536.  Inputs with `p` near 1 and few panels must return status
2.  The test records the relative width of each interval.  The module test compares the module
with native Lean bit for bit on generated inputs, rejected and unfinished ones among them.

### Samples

The reference radii of the samples come from `mpmath` at 30 digits for the circular error and 40
for the linear error.

| Entry | Inputs | Reference radius |
|---|---|---|
| `circularError` | `m = (0, 0)`, `C = (1, 0, 1)`, `p = 0.9` | `2.1459660262893472` |
| `circularError` | `m = (3, 0)`, `C = (1, 0, 1)`, `p = 0.9` | `4.4197039765207454` |
| `circularError` | `m = (0, 0)`, `C = (1, 0, 10000)`, `p = 0.9` | `164.48840265940297` |
| `circularError` | `m = (0, 3)`, `C = (1, 0, 100)`, `p = 0.9` | `17.203772037523088` |
| `circularError` | `m = (2, -1)`, `C = (25, 6, 16)`, `p = 0.9` | `10.315504204502985` |
| `linearError` | `b = 0`, `v = 1`, `p = 0.9` | `1.6448536269514727` |
| `linearError` | `b = 1`, `v = 1`, `p = 0.9` | `2.2844680121686749` |
| `linearError` | `b = 3`, `v = 4`, `p = 0.9` | `5.5632088625179973` |
| `linearError` | `b = 0`, `v = 1`, `p = 0.5` | `0.67448975019608174` |
| `linearError` | `b = 0.5`, `v = 0.25`, `p = 0.99` | `1.6633160050017200` |

### What lies outside the theorems

The theorems concern the radius of the normal model.  Whether the errors are normal, the realism
of the covariance and the bias, the agreement of their frames, and the choice of `p` are the
caller's.  The theorems bound no width: an accepted interval is sound however wide, and status 2
carries no statement.  The program reaches no conclusion when `p` lies closer to 1 than the
enclosure's width allows, and the interval of the circular error is about `7/n` to `11/n` of the
radius wide at `p = 0.9`.
