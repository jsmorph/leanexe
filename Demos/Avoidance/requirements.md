# Avoidance maneuver authorizer requirements

## Purpose and scope

An unproved planner proposes an impulsive burn for a spacecraft, the primary, that faces one or more conjunctions with other objects, the secondaries.  The program accepts the burn only when a proved upper bound on the two-dimensional probability of collision after the burn lies below a threshold, for every listed conjunction and for every velocity change in a box that models the burn's execution error.  It follows the authorizer structure of [the energy demo](../Energy/README.md) and [the passive-safety demo](../PassiveSafety/README.md): the planner proposes, the program accepts or rejects, and the theorems cover accepted results only.

The first version leaves out the claim that the burn creates no new conjunction.  With other objects that claim is catalog screening.  With a listed secondary at another time it is pairwise screening of the trajectory after the burn over a box of states, which the screening demo's isolation does not enclose, since it takes classical elements, and its theorem would need the isolation over the propagation of this demo.  The first version also leaves out finite burns, errors in the time of the burn, perturbations of the burn's effect except through a padding of the position, an error in the relative velocity, a change of the covariance by the burn, the rotation of covariances from each object's RTN frame into the inertial frame, and the parsing of conjunction data messages.  The program is a ground program compiled to WebAssembly.

## The two-body propagation

The primary's state just before the burn is the position `r_b` in km and the velocity `v_b` in km/s at the burn time `t_b`, in an inertial frame, and the burn adds the velocity change `Δv` in km/s.  With the gravitational parameter `μ` in km³/s², the two-body state at `t` seconds after a state `(r₀, v₀)` is `Φ(μ, r₀, v₀, t)`, defined by the Lagrange coefficients `f` and `g` in terms of the change of the eccentric anomaly:

| Quantity | Definition |
|---|---|
| `R₀`, `D`, `V²` | `\|r₀\|`, `r₀ · v₀`, `v₀ · v₀` |
| `α` | `2/R₀ − V²/μ`, the inverse of the semimajor axis |
| `q`, `ω` | `√(α/μ)` and `μ α q`, the mean motion `√(μ α³)` in radians per second |
| `a_k`, `b_k` | `1 − R₀ α` and `−D q`, which equal `e cos E₀` and `−e sin E₀` |
| `ΔE` | The root of `ΔE + b_k cos ΔE − a_k sin ΔE = ω t + b_k`, unique when `e² = a_k² + b_k² < 1` |
| `c`, `s`, `w` | `cos ΔE`, `sin ΔE`, and `1 − a_k c − b_k s`, which equals `α \|r(t)\|` |
| `f`, `g` | `1 − (1 − c)/(R₀ α)` and `(R₀ α s + D q (1 − c))/ω` |
| `ḟ`, `ġ` | `−α s/(q w R₀)` and `1 − (1 − c)/w` |
| `Φ` | The position `f r₀ + g v₀` and the velocity `ḟ r₀ + ġ v₀` |

The equation for `ΔE` is Kepler's equation in the form of SGP4, `E + b cos E − a sin E = ℓ`, whose root `Demos.Sgp4.Kepler.root a b ℓ` the screening demo also uses, with `a = a_k`, `b = b_k`, and `ℓ = ω t + b_k`.  The expression for `g` follows from Kepler's equation and contains no difference of large terms.  The model takes `Φ` as its definition, `Demos.Avoidance.propagate`, and theorem M2 states that for `μ > 0`, `α > 0`, and `e² < 1`, the position and velocity of `t ↦ Φ(μ, r₀, v₀, t)` solve Newton's equation `r'' = −μ r/|r|³` at every real `t`, in the sense of `Demos.Orbit.Newton` of the orbit-determination demo.  Theorem M1 states that `Φ` at `t = 0` is `(r₀, v₀)`.

## The encounter after the burn

Conjunction `j` has a reference time `t_j`, the time of closest approach of a conjunction data message, with `Δt_j = t_j − t_b > 0`.  At `t_j` it gives the nominal state `(r₁, v₁)` of the primary without the burn, the state `(r₂, v₂)` of the secondary, the combined covariance `C` of the two position errors in km² in the same inertial frame, and the combined hard-body radius `R_j` in km.  The burn's effect on the primary at `t_j` is the difference of two two-body propagations from the burn time, and the relative position `ρ` and velocity `ν` after the burn are

`(p₁, u₁) = Φ(μ, r_b, v_b + Δv, Δt_j)`,  `(p₀, u₀) = Φ(μ, r_b, v_b, Δt_j)`,
`ρ = r₁ − r₂ + (p₁ − p₀) + d`,  `ν = v₁ − v₂ + (u₁ − u₀)`.

The vector `d` is a displacement with `|d_x|, |d_y|, |d_z| ≤ P` for the padding `P ≥ 0` in km.  The nominal states come from the operator's propagator, and only the change made by the burn comes from the two-body model, so a zero burn reproduces the message's geometry.  Theorem M5 states that when the nominal state of the primary is the two-body propagation `Φ(μ, r_b, v_b, Δt_j)`, `ρ − d` and `ν` are the relative state of the two-body trajectory after the burn.  The padding covers, by the caller's premise, the distance between the true post-burn relative position at `t_j` and the model's, and the relative velocity is the model's by premise.

The encounter follows the short-encounter model of the conjunction demo: the relative motion is the straight line `ρ + τ ν`, the encounter plane is perpendicular to `ν`, and the miss vector is the point of the line nearest the origin.  The plane's axes come from `ν` and the primary's nominal position `r₁`:

`x = r₁ × ν`,  `x̂ = x/|x|`,  `ẑ = ν/|ν|`,  `ŷ = ẑ × x̂`,
`m = (ρ · x̂, ρ · ŷ)`,  `C_p = (x̂ᵀ C x̂, x̂ᵀ C ŷ, ŷᵀ C ŷ)`.

Theorem M3 states that for `|x| > 0` and `|ν| > 0`, `x̂` and `ŷ` are unit vectors perpendicular to each other and to `ν`, and theorem M4 that `m₁² + m₂² ≤ |ρ + τ ν|²` for every real `τ`, with equality at `τ = −(ρ · ν)/(ν · ν)`.  The probability of collision after the burn is `Pc_j(Δv, d) = Demos.Conjunction.Model.pc m₁ m₂ c₁₁ c₁₂ c₂₂ R_j`, the integral of the Gaussian density with mean `m` and covariance `C_p` over the disk of radius `R_j` in the plane.  The covariance is the message's and does not change with the burn.  The probability does not depend on the choice of orthonormal axes in the plane, since a rotation of the plane maps the disk onto itself.  No theorem of the first version states this invariance, and the axes above fix the definition.

The burn moves the time of closest approach to `t_j + τ*` with `τ* = −(ρ · ν)/(ν · ν)`, and the straight line through the state at `t_j` follows the two-body relative motion only near `t_j`.  The review compared the line's miss with the two-body closest approach: for `|τ*|` up to 5 s, at 10 and 1 km/s, they agree to 7 mm and the probabilities to `3 × 10⁻⁴` relative.  At 1 km/s with `τ* = 260` s they differ by 365 m, and at 10 km/s with `τ* = 26` s by 4.2 m and a factor of 2.4 in the probability.  No input bounds `τ*`.

## Execution error

The execution error enters as a box of velocity changes in the inertial frame: `Δv_x ∈ [lx, hx]`, `Δv_y ∈ [ly, hy]`, and `Δv_z ∈ [lz, hz]`.  Every velocity change in the box is a burn that the theorem covers, with no assumption on its distribution, and the caller places the proposed burn in the box.  An error stated as magnitude and pointing in the spacecraft's frame enters through an inertial box that encloses it, which the caller computes.

## Interface

The module exports `authorize`, which takes an array of binary64 values and the panel count `N`, and `pcBox`, the probability enclosure for interval means and covariances.

| Input index | Value | Requirement |
|---|---|---|
| 0 | `μ` (km³/s²) | `μ > 0` |
| 1 to 3 | `r_b` (km) | |
| 4 to 6 | `v_b` (km/s) | |
| 7 to 12 | `lx`, `hx`, `ly`, `hy`, `lz`, `hz` (km/s) | `lx ≤ hx`, `ly ≤ hy`, `lz ≤ hz` |
| 13 | `P` (km) | `P ≥ 0` |
| 14 | Threshold `T` | |
| `15 + 20j` | `Δt_j` (s) | `Δt_j > 0` |
| `16 + 20j` to `18 + 20j` | `r₁` (km) | |
| `19 + 20j` to `21 + 20j` | `v₁` (km/s) | |
| `22 + 20j` to `24 + 20j` | `r₂` (km) | |
| `25 + 20j` to `27 + 20j` | `v₂` (km/s) | |
| `28 + 20j` to `33 + 20j` | `C_xx`, `C_xy`, `C_xz`, `C_yy`, `C_yz`, `C_zz` (km²) | |
| `34 + 20j` | `R_j` (km) | `R_j > 0` |

Every value must be finite, and the array must hold `15 + 20K` values for `1 ≤ K ≤ 64` conjunctions.  The panel count `N`, a `UInt64` argument, must lie from 1 to 1,048,576, the range of `Demos.Conjunction.pcWith`.  The covariance has no requirement: a covariance whose projection the arithmetic does not show positive definite gives verdict 2.  An input that breaks a requirement gives the output `1, 0`.

| Output index | Value |
|---|---|
| 0 | Status |
| 1 | `K` |
| `2 + 3j` | Verdict of conjunction `j` |
| `3 + 3j`, `4 + 3j` | `lo_j` and `hi_j`, an interval that contains `Pc_j(Δv, d)` for every `Δv` in the box and every `d` within the padding, or zeros when the enclosure is rejected |

| Status | Meaning |
|---|---|
| 0 | Accepted: every conjunction has verdict 0. |
| 1 | Invalid input. |
| 2 | Rejected: no conjunction has verdict 2, and some conjunction has verdict 1. |
| 3 | Rejected: some conjunction has verdict 2. |

| Verdict | Meaning |
|---|---|
| 0 | The enclosure was accepted, and `hi_j < T`. |
| 1 | The enclosure was accepted, and `hi_j ≥ T`. |
| 2 | The enclosure was rejected: a post-burn or nominal orbit not shown bound with `e² < 1`, `\|x\|` or `\|ν\|` not shown positive, the projected covariance not shown positive definite, or an interval operation that rejected. |

`pcBox` takes, in order, the lower and upper ends of `m₁`, `m₂`, `c₁₁`, `c₁₂`, and `c₂₂`, the radius `r`, and `N`, and returns a status, `lo`, and `hi`.  Status 0 implies that `[lo, hi]` contains `Model.pc` for every point of the five intervals.  Status 1, with zero ends, marks an end that is not finite, a lower end above its upper end, a `c₁₁` without a positive lower end, an `r` that is not positive, an `N` outside its range, or an interval operation that rejected.

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding.  For conjunction `j` it evaluates the model of the two sections above with the box of velocity changes, the intervals `[−P, P]` of the components of `d`, and every other input as a point interval, so each resulting interval contains the model's value for every point of the box and of the padding.  It states the propagation, the relative state, and the plane with [`enclosure_def`](../../Library/Numerics/Interval/README.md#one-source-for-a-real-function-and-its-interval-program), which declares each real function, its interval function, and the theorem that the interval function encloses it.  The root of Kepler's equation, `keplerRoot`, is an approximate root in binary64, widened by its residual over the least slope `1 − √(a_k² + b_k²)`, as in `Demos.Sgp4.Kepler.rootI`, with the sum of squares clamped at zero before the square root.  The outward-rounded square of an interval that holds 0, even `[0, 0]`, has the lower end `−4.9 × 10⁻³²⁴`, which `sqrt` rejects, so `rootI` rejects a circular orbit.

The program computes the projected covariance in a form centered at points `g` and `h` near the axes, the middles of the intervals of `x̂` and `ŷ`: `x̂ᵀ C x̂ = gᵀ C g + 2 (x̂ − g)ᵀ C g + (x̂ − g)ᵀ C (x̂ − g)`, and alike for `x̂ᵀ C ŷ` and `ŷᵀ C ŷ`.  The form is an identity over the reals, which `project_eq` states.  In the natural form, the interval of `C x̂` carries the largest variance of `C`, often along the track, times the width of `x̂`, and the review found conditional variances from `−0.0016` to `0.0068` and 28 of 72 settings rejected that the centered form rejects 6 of.

The program also encloses `α` and `e²` of both propagated states, `x · x`, and `ν · ν`, and it accepts the enclosure only when the lower ends of `α`, `x · x`, and `ν · ν` are positive and the upper end of `e²` is below 1, so that M2 and M3 apply to every point of the box.

The probability enclosure for interval inputs, `pcBoxWith` in `Demos/Conjunction/Box.lean`, is the panel method of `Demos.Conjunction.pcWith` with the five scalar inputs replaced by intervals: the setup computes `2 c₁₁`, `c₁₂/c₁₁`, `√(c₂₂ − c₁₂²/c₁₁) √2`, and `r²` from the intervals, and the panels are those of `pcWith`.  It rejects unless the interval of `c₁₁` is accepted with a positive lower end, `r > 0`, and `1 ≤ N ≤ 2²⁰`.  As in `pcWith`, `sqrt` rejects a conditional variance with a negative lower end and the division by `√(c₂₂ − c₁₂²/c₁₁) √2` one that holds 0, so an accepted enclosure has a positive conditional variance.  The existing `pc` and `assess`, the module `conjunction`, and its theorems stay unchanged.

A conjunction costs two propagations, a few hundred interval operations, and one call of `pcBoxWith` with `N` panels, each of which evaluates `exp` twice and `erf` four times.  A call costs `K` such conjunctions, at most `64 · 2²⁰` panels, and the tests measure the time.  The output holds `2 + 3K` values, at most 194.

## Theorems

| Code | Layer | Statement |
|---|---|---|
| M1 | Model | For `μ > 0`, `α > 0`, and `e² < 1`, `Φ(μ, r₀, v₀, 0) = (r₀, v₀)`. |
| M2 | Model | For `μ > 0`, `α > 0`, and `e² < 1`, the position and velocity of `t ↦ Φ(μ, r₀, v₀, t)` satisfy `Demos.Orbit.Newton μ`: the position stays away from the origin, its derivative is the velocity, and the velocity's derivative is `−μ r/\|r\|³`, at every real `t`. |
| M3 | Model | For `x · x > 0` and `ν · ν > 0`, `x̂ · x̂ = ŷ · ŷ = 1` and `x̂ · ŷ = x̂ · ν = ŷ · ν = 0`. |
| M4 | Model | Under the hypotheses of M3, `m₁² + m₂² ≤ \|ρ + τ ν\|²` for every real `τ`, with equality at `τ = −(ρ · ν)/(ν · ν)`. |
| M5 | Model | When `(r₁, v₁) = Φ(μ, r_b, v_b, Δt_j)`, `ρ − d = p₁ − r₂` and `ν = u₁ − v₂`. |
| P1 | Program | For intervals of `m₁`, `m₂`, `c₁₁`, `c₁₂`, and `c₂₂`, an accepted result of `pcBoxWith` has finite ends, and every real point of the intervals has `c₁₁ > 0`, `c₁₁ c₂₂ − c₁₂² > 0`, and `lo ≤ Model.pc ≤ hi`. |
| A1 | Program | For status 0, the input is valid, and for every conjunction `j`, every `Δv` in the box, and every `d` with `\|d_x\|, \|d_y\|, \|d_z\| ≤ P`: both propagated states have `α > 0` and `e² < 1`, `x · x > 0`, `ν · ν > 0`, the projected covariance is positive definite, and `Pc_j(Δv, d) < T`, for the real values of the inputs.  With M2 and M4, the two-body trajectories with and without `Δv` solve Newton's equation and the miss vector is the closest approach of the line. |
| A2 | Program | For a valid input and every `j < K`, a verdict other than 2 gives the conditions of A1 and `lo_j ≤ Pc_j(Δv, d) ≤ hi_j` for every `Δv` and `d` as in A1, and verdict 0 gives `Pc_j(Δv, d) < T`. |
| A3 | Program | Status 1 holds exactly for the inputs that break a requirement. |
| C1 | Compilation | The export `authorize`, called from a ready store with room for the generated allocation bound, returns the bit patterns of `authorize` without a trap, and A1 applies to its status 0.  The export `pcBox` returns the words of `pcBox` without a trap from every ready store, and P1 applies to its status 0. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  A program that rejects every burn satisfies A1, A2, and P1, and the tests check the statuses that the cases fix.

## Tests

An independent oracle in Python with mpmath, written apart from the program, checks the module's outputs.  It propagates each state with its own two-body solution: the classical elements of the state, Kepler's equation `E − e sin E = M` solved by Newton's method at 40 digits, and the state at the new anomaly, and it compares this propagation with a Runge–Kutta integration of Newton's equation on five states.  It forms the relative state, takes the plane's axes from the coordinate axis least aligned with `ν`, and computes the probability as an integral over the angle of the radial integral along each ray from the disk's center, which has a closed form in `exp` and `erf`, by the trapezoid rule with the points doubled until two values agree to `10⁻²⁵`.  It compares that integral with mpmath's two-dimensional quadrature on three inputs.

For each conjunction the oracle samples the eight corners of the box, each with a corner of the padding, the center, and six random points of both, and climbs from the largest sample by a compass search inside the box and the padding.  The test requires:

- the output `1, 0` exactly for the invalid inputs, and an output of `2 + 3K` values otherwise;
- status 0 exactly when every verdict is 0, and status 3 exactly when some verdict is 2;
- verdict 0 exactly when `hi_j < T` among the accepted enclosures, and zero ends for verdict 2;
- for every conjunction with verdict 0 or 1, every sampled probability in `[lo_j, hi_j]`;
- for status 0, every sampled probability below `T`;
- a verdict other than 0 for a conjunction with a sampled probability above `10 T`;
- the status and the verdicts that each case fixes in advance from the oracle's margins.

After the first run it builds, for an accepted conjunction of each case, inputs whose threshold is `hi_j`, the next double above `hi_j`, and a value between `lo_j` and `hi_j`, and requires verdicts 1, 0, and 1.  A mutation run alters correct outputs and requires the checks to fail on each.  The tests record the ratio of `hi_j` to the largest sampled probability.  A module test compares the WebAssembly module with native Lean on generated inputs, bit for bit.

The cases include a burn that moves the miss of a high-probability conjunction from 30 m to kilometers, the zero burn, two and three conjunctions of which one fails, an equatorial, a polar, a circular, and an eccentric primary with `e = 0.3`, a secondary on a crossing orbit at 10 km/s and one at 1 km/s, a reference time a day after the burn, boxes from `±10⁻⁶` to `±10⁻³` km/s, `P > 0`, an elongated covariance with an aspect ratio of 100, and a nominal state 1 km from the two-body one.  Point boxes with the secondary near the trajectory after the burn give probabilities near `10⁻²`, from states away from the apsides, so that an error in `Φ` moves the probability far: at 600, 8,000, and 86,400 s for a low orbit with `e = 0.01`, and at 8,000 s for an equatorial, a circular, and an eccentric orbit.  Two such cases put 5 km of `ρ` along `ν`, at 10 and 1 km/s, and one has a padding of 100 m.  A box holds the burn that cancels the miss at its center.  A negative definite covariance and a covariance indefinite along `ν` with a positive definite projection test the covariance, and a relative velocity parallel to `r₁`, an unbound orbit after the burn, a case with one rejected and one high conjunction, and every invalid condition test the statuses.

## What lies outside the theorems

The theorems concern the model.  The short-encounter assumptions of the conjunction demo, rectilinear relative motion during the encounter, Gaussian position errors constant during it, independent errors, and spherical objects, are not proved, and the line through the state at `t_j` follows the motion only near `t_j`.  The two-body change of the trajectory by the burn neglects perturbations, which enter only through the padding `P`, the caller's premise.  The states, the covariance, the radius, the threshold, the box, and the agreement of frames and epochs are the caller's.  The theorems bound no width: an accepted enclosure is sound however wide, and a wide one rejects a safe burn with status 2.  No theorem states that the burn creates no new conjunction.
