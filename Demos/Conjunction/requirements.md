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
