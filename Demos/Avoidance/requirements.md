# Avoidance maneuver authorizer requirements

## Purpose and scope

An unproved planner proposes an impulsive burn for a spacecraft, the primary, that faces one or more conjunctions with other objects, the secondaries.  The program accepts the burn only when a proved upper bound on the two-dimensional probability of collision after the burn lies below a threshold, for every listed conjunction and for every velocity change in a box that models the burn's execution error.  It subdivides the box into cells for each conjunction, so that the bound over the box is the largest of the bounds over the cells.  It follows the authorizer structure of [the energy demo](../Energy/README.md) and [the passive-safety demo](../PassiveSafety/README.md): the planner proposes, the program accepts or rejects, and the theorems cover accepted results and the conjunctions that the program shows at or above the threshold.

The program leaves out the claim that the burn creates no new conjunction.  With other objects that claim is catalog screening.  With a listed secondary at another time it is pairwise screening of the trajectory after the burn over a box of states, which the screening demo's isolation does not enclose, since it takes classical elements, and its theorem would need the isolation over the propagation of this demo.  It also leaves out finite burns, errors in the time of the burn, perturbations of the burn's effect except through a padding of the position, an error in the relative velocity, a change of the covariance by the burn, the rotation of covariances from each object's RTN frame into the inertial frame, and the parsing of conjunction data messages.  The program is a ground program compiled to WebAssembly.

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

Theorem M3 states that for `|x| > 0` and `|ν| > 0`, `x̂` and `ŷ` are unit vectors perpendicular to each other and to `ν`, and theorem M4 that `m₁² + m₂² ≤ |ρ + τ ν|²` for every real `τ`, with equality at `τ = −(ρ · ν)/(ν · ν)`.  The probability of collision after the burn is `Pc_j(Δv, d) = Demos.Conjunction.Model.pc m₁ m₂ c₁₁ c₁₂ c₂₂ R_j`, the integral of the Gaussian density with mean `m` and covariance `C_p` over the disk of radius `R_j` in the plane.  The covariance is the message's and does not change with the burn.  The probability does not depend on the choice of orthonormal axes in the plane, since a rotation of the plane maps the disk onto itself.  No theorem states this invariance, and the axes above fix the definition.

The burn moves the time of closest approach to `t_j + τ*` with `τ* = −(ρ · ν)/(ν · ν)`, and the straight line through the state at `t_j` follows the two-body relative motion only near `t_j`.  The review compared the line's miss with the two-body closest approach: for `|τ*|` up to 5 s, at 10 and 1 km/s, they agree to 7 mm and the probabilities to `3 × 10⁻⁴` relative.  At 1 km/s with `τ* = 260` s they differ by 365 m, and at 10 km/s with `τ* = 26` s by 4.2 m and a factor of 2.4 in the probability.  No input bounds `τ*`.

## Execution error

The execution error enters as a box of velocity changes in the inertial frame: `Δv_x ∈ [lx, hx]`, `Δv_y ∈ [ly, hy]`, and `Δv_z ∈ [lz, hz]`.  Every velocity change in the box is a burn that the theorem covers, with no assumption on its distribution, and the caller places the proposed burn in the box.  An error stated as magnitude and pointing in the spacecraft's frame enters through an inertial box that encloses it, which the caller computes.

## Interface

The module exports `authorize`, which takes an array of binary64 values, the panel count `N`, and the split budget `S`, and `pcBox`, the probability enclosure for interval means and covariances.

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

Every value must be finite, and the array must hold `15 + 20K` values for `1 ≤ K ≤ 64` conjunctions.  The panel count `N`, a `UInt64` argument, must lie from 1 to 1,048,576, the range of `Demos.Conjunction.pcWith`, and the split budget `S`, a `UInt64` argument, from 0 to 65,536.  The covariance has no requirement: a covariance whose projection the arithmetic does not show positive definite gives verdict 2.  An input that breaks a requirement gives the output `1, 0`.

| Output index | Value |
|---|---|
| 0 | Status |
| 1 | `K` |
| `2 + 3j` | Verdict of conjunction `j` |
| `3 + 3j`, `4 + 3j` | `lo_j` and `hi_j`, the hull of the search of conjunction `j`, an interval that contains `Pc_j(Δv, d)` for every `Δv` in the box and every `d` within the padding, or zeros when the hull is rejected |

| Status | Meaning |
|---|---|
| 0 | Accepted: every conjunction has verdict 0. |
| 1 | Invalid input. |
| 2 | Rejected: no conjunction has verdict 2, and some conjunction has verdict 1. |
| 3 | Rejected: some conjunction has verdict 2. |
| 4 | Rejected: no conjunction has verdict 1 or 2, and some conjunction has verdict 3. |

| Verdict | Meaning |
|---|---|
| 0 | The hull was accepted, and `hi_j < T`. |
| 1 | The hull was accepted, `hi_j ≥ T`, and the interval of a cell or of a probe was accepted with a lower end at or above `T`. |
| 2 | The hull was rejected: for some cell, a post-burn or nominal orbit not shown bound with `e² < 1`, `\|x\|` or `\|ν\|` not shown positive, the projected covariance not shown positive definite, or an interval operation that rejected. |
| 3 | The hull was accepted, `hi_j ≥ T`, and no interval of a cell or of a probe was accepted with a lower end at or above `T`: the search ran out of splits, or reached cells that it cannot split. |

`pcBox` takes, in order, the lower and upper ends of `m₁`, `m₂`, `c₁₁`, `c₁₂`, and `c₂₂`, the radius `r`, and `N`, and returns a status, `lo`, and `hi`.  Status 0 implies that `[lo, hi]` contains `Model.pc` for every point of the five intervals.  Status 1, with zero ends, marks an end that is not finite, a lower end above its upper end, a `c₁₁` without a positive lower end, an `r` that is not positive, an `N` outside its range, or an interval operation that rejected.

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding.  For conjunction `j` it evaluates the model of the two sections above over a cell, a box of velocity changes inside the input's box, with the intervals `[−P, P]` of the components of `d` and every other input as a point interval, so each resulting interval contains the model's value for every point of the cell and of the padding.  The next section describes the search over the cells.  It states the propagation, the relative state, and the plane with [`enclosure_def`](../../Library/Numerics/Interval/README.md#one-source-for-a-real-function-and-its-interval-program), which declares each real function, its interval function, and the theorem that the interval function encloses it.  The root of Kepler's equation, `keplerRoot`, is an approximate root in binary64, widened by its residual over the least slope `1 − √(a_k² + b_k²)`, as in `Demos.Sgp4.Kepler.rootI`, with the sum of squares clamped at zero before the square root.  The outward-rounded square of an interval that holds 0, even `[0, 0]`, has the lower end `−4.9 × 10⁻³²⁴`, which `sqrt` rejects, so `rootI` rejects a circular orbit.

The program computes the projected covariance in a form centered at points `g` and `h` near the axes, the middles of the intervals of `x̂` and `ŷ`: `x̂ᵀ C x̂ = gᵀ C g + 2 (x̂ − g)ᵀ C g + (x̂ − g)ᵀ C (x̂ − g)`, and alike for `x̂ᵀ C ŷ` and `ŷᵀ C ŷ`.  The form is an identity over the reals, which `project_eq` states.  In the natural form, the interval of `C x̂` carries the largest variance of `C`, often along the track, times the width of `x̂`, and the review found conditional variances from `−0.0016` to `0.0068` and 28 of 72 settings rejected that the centered form rejects 6 of.

The program also encloses `α` and `e²` of both propagated states, `x · x`, and `ν · ν`, and it accepts the enclosure only when the lower ends of `α`, `x · x`, and `ν · ν` are positive and the upper end of `e²` is below 1, so that M2 and M3 apply to every point of the box.

The probability enclosure for interval inputs, `pcBoxWith` in `Demos/Conjunction/Box.lean`, is the panel method of `Demos.Conjunction.pcWith` with the five scalar inputs replaced by intervals: the setup computes `2 c₁₁`, `c₁₂/c₁₁`, `√(c₂₂ − c₁₂²/c₁₁) √2`, and `r²` from the intervals, and the panels are those of `pcWith`.  It rejects unless the interval of `c₁₁` is accepted with a positive lower end, `r > 0`, and `1 ≤ N ≤ 2²⁰`.  As in `pcWith`, `sqrt` rejects a conditional variance with a negative lower end and the division by `√(c₂₂ − c₁₂²/c₁₁) √2` one that holds 0, so an accepted enclosure has a positive conditional variance.  The existing `pc` and `assess`, the module `conjunction`, and its theorems stay unchanged.

An evaluation costs two propagations, a few hundred interval operations, and one call of `pcBoxWith` with `N` panels, each of which evaluates `exp` twice and `erf` four times.  A conjunction costs at most `2S + 1` evaluations of cells and as many probes, a call `K` conjunctions, and the tests measure the time.  The output holds `2 + 3K` values, at most 194.

## The search over the box

Over the whole box, the interval of the miss vector is the projection of a box of relative positions, and when the burn's effect lies along a direction oblique to the axes it holds positions far from the true range, which grows with the time from the burn and the size of the box.  With a box of `±1` cm/s 2,700 s before the encounter, the upper end over the whole box exceeds the threshold `10⁻⁴` while the largest probability over the box lies below a tenth of it.  The program therefore subdivides the box of velocity changes for each conjunction and evaluates the model over each cell.

A cell is a box of velocity changes inside the input's box, with an interval and a depth.  The search of conjunction `j` keeps a list of cells, which starts with the input's box, a rejected interval, and depth 0, and evaluates the cells in the order of their creation.  The evaluation of a cell gives an interval `r` that contains `Pc_j(Δv, d)` for every `Δv` of the cell and every `d` within the padding, or a rejected interval, and the search takes the first of these steps that applies:

1. When `r` is accepted with `hi < T`, the search adds `r` to the hull.
2. When `r` is accepted with `lo ≥ T`, it adds `r` to the hull and stops.
3. When splits remain, the cell's depth is a multiple of 3, and the middle of each of its sides is finite and lies on the side, it evaluates the probe, the interval of the point box at the cell's center with the padding 0.  When the probe is accepted with `lo ≥ T`, it adds `r` to the hull and stops.
4. When splits remain and the middle of the cell's longest side is finite and lies strictly between the side's ends, it splits the cell at that middle into a lower and an upper half, each with the interval `r` and the cell's depth plus 1, appends both to the list, and spends one split.
5. Otherwise it adds `r` to the hull.

The search also stops when it has evaluated every cell of the list, or after `2S + 1` evaluations of cells, which suffice to evaluate every cell, since `S` splits append `2S` cells to the first.  At every stop it adds to the hull the intervals of the cells not evaluated.  The hull is the interval from the least lower end to the greatest upper end of the intervals added, rejected when one of them is rejected.  Every `Δv` of the box lies in a cell evaluated and not split, or in a cell not evaluated, whose interval comes from the evaluation of the cell that it was split from, so an accepted hull contains `Pc_j(Δv, d)` for every `Δv` of the box and every `d` within the padding.

The middle of a side `[a, b]` is `a + (b − a) · 0.5` in binary64, the screening demo's `middle`, and the longest side is the one with the largest difference of ends in km/s, the first in the order x, y, z among equal differences.  A cell's lower end reaches `T` only when the probability varies little over the cell, so without probes an unsafe burn with a wide box spends the whole budget.  The probe at `d = 0` shows the probability at or above `T` for one velocity change and one displacement, which suffices to reject the burn, and it applies to every cell that steps 1 and 2 leave undecided, among them a point box whose padding widens its interval.  For a cube, three splits of the longest side halve each side once, so a probe at each third depth probes once for each halving of every side, and a box with unequal sides is split along its longest side until its sides are comparable.  A probe that stops the search adds the cell's own interval `r`, since the probe's interval holds only at the center, so a conjunction whose stopping cell has a rejected `r` gets verdict 2.  With `S = 0` the search evaluates the input's box once.

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
| A4 | Program | For a valid input and every `j < K`, verdict 1 gives a `Δv` in the box at which, with `d = 0`, the conditions of A1 hold and `Pc_j(Δv, 0) ≥ T`.  Status 2 gives a valid input and such a `Δv` for some `j`. |
| C1 | Compilation | The export `authorize`, called with the array, `N`, and `S` from a ready store with room for the generated allocation bound, returns the bit patterns of `authorize` without a trap, and A1 applies to its status 0.  The export `pcBox` returns the words of `pcBox` without a trap from every ready store, and P1 applies to its status 0. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  A program that rejects every burn with verdict 3 satisfies A1, A2, A4, and P1, and the tests check the statuses that the cases fix and replay the search.

## Tests

An independent oracle in Python with mpmath, written apart from the program, checks the module's outputs.  It propagates each state with its own two-body solution: the classical elements of the state, Kepler's equation `E − e sin E = M` solved by Newton's method at 40 digits, and the state at the new anomaly, and it compares this propagation with a Runge–Kutta integration of Newton's equation on five states.  It forms the relative state, takes the plane's axes from the coordinate axis least aligned with `ν`, and computes the probability as an integral over the angle of the radial integral along each ray from the disk's center, which has a closed form in `exp` and `erf`, by the trapezoid rule with the points doubled until two values agree to `10⁻²⁵`.  It compares that integral with mpmath's two-dimensional quadrature on three inputs.

For each conjunction the oracle samples the eight corners of the box, each with a corner of the padding, the center, and six random points of both, and climbs from the largest sample by a compass search inside the box and the padding.  The test requires:

- the output `1, 0` exactly for the invalid inputs, and an output of `2 + 3K` values otherwise;
- status 0 exactly when every verdict is 0, status 3 exactly when some verdict is 2, status 2 exactly when some verdict is 1 and none is 2, and status 4 otherwise;
- verdict 0 exactly when `hi_j < T` among the accepted hulls, and zero ends for verdict 2;
- for every conjunction with verdict 0, 1, or 3, every sampled probability in `[lo_j, hi_j]`;
- for status 0, every sampled probability below `T`;
- a verdict other than 0 for a conjunction with a sampled probability above `10 T`;
- for verdict 1, a probability at or above `T` that the oracle finds by its samples and compass search;
- the status and the verdicts that each case fixes in advance from the oracle's margins;
- the output that a replay of the search computes, bit for bit, and for verdict 1 the oracle's probability at or above `T` at the replay's witness with `d = 0`.

The replay follows the section on the search with the module's own evaluation of each cell and each probe, a call with `S = 0`, the cell or the point box as the box, the padding or 0, and the one conjunction, so that it checks the search's steps, splits, budget, stops, and hull, while the other checks test the evaluations.  Its witness of a verdict 1 is the lower corner of the cell whose interval reached `T`, or the center of the probe that did.  After the first run the oracle calls each valid case with `S = 0` and builds, from the output of that call for an accepted conjunction, inputs with `S = 0` whose threshold is `hi_j`, the next double above `hi_j`, a value between `lo_j` and `hi_j`, `lo_j`, and the next double above `lo_j`, and requires the verdict of a single evaluation: 0 when `hi_j < T`, 1 when `lo_j ≥ T`, and 3 otherwise.  It also builds an input with `S = 1` whose threshold is that `hi_j`, which the replay checks.  A mutation run alters correct outputs and requires the checks to fail on each.  The tests record the ratio of `hi_j` to the largest sampled probability.  A module test compares the WebAssembly module with native Lean on generated inputs, bit for bit.

The cases include a burn that moves the miss of a high-probability conjunction from 30 m to kilometers, the zero burn, two and three conjunctions of which one fails, an equatorial, a polar, a circular, and an eccentric primary with `e = 0.3`, a secondary on a crossing orbit at 10 km/s and one at 1 km/s, a reference time a day after the burn, boxes from `±10⁻⁶` to `±10⁻³` km/s, `P > 0`, an elongated covariance with an aspect ratio of 100, and a nominal state 1 km from the two-body one.  Point boxes with the secondary near the trajectory after the burn give probabilities near `10⁻²`, from states away from the apsides, so that an error in `Φ` moves the probability far: at 600, 8,000, and 86,400 s for a low orbit with `e = 0.01`, and at 8,000 s for an equatorial, a circular, and an eccentric orbit.  Two such cases put 5 km of `ρ` along `ν`, at 10 and 1 km/s, and one has a padding of 100 m.  A box holds the burn that cancels the miss at its center.  A negative definite covariance and a covariance indefinite along `ν` with a positive definite projection test the covariance, and a relative velocity parallel to `r₁`, an unbound orbit after the burn, a case with one rejected and one high conjunction, and every invalid condition test the statuses.

The cases run with a budget of 64 unless they name another.  The elongated covariance with a box of `±1` m/s and `T = 0.02`, whose interval over the whole box is rejected and whose largest probability that the oracle finds is `2.4 × 10⁻⁴`, requires status 0, and so does the relative velocity parallel to `r₁` with the box of `±1` mm/s and `T = 0.1`, whose interval over the whole box is rejected too.  The relative velocity parallel to `r₁` with the zero burn requires verdict 2, a rejection of `|x|` at every budget.  The box of `±1` cm/s 2,700 s before the encounter and the box of `±1` mm/s a day before an encounter with a cross-track deviation of 10 km require status 0 with a budget of 256 and with their least budgets, 13 and 5, and status 4 with the budgets 12 and 4 below them and with `S = 0`.  The box of `±1` cm/s also requires status 4 with a budget of 2.  The box of `±1` cm/s with a second conjunction at a miss of 600 m requires verdicts 3 and 1 and status 2 with `S = 1`, and verdicts 3 and 3 and status 4 with `S = 0`.  A box across the escape speed 60 s before the encounter, wide in `y` only, has cells accepted below the speed and rejected above it, and requires status 3 with a budget of 256.  The zero burn with a padding of 100 m requires verdict 1 from the probe of the point box.  A box with sides of 8, 2, and 2 × 10⁻⁵ km/s and the box about the burn that cancels the miss with a padding of 100 m and `T = 0.02` fix no status, and the replay checks them.  The cases accepted with the threshold `10⁻⁴` are repeated with the threshold at 2 and at 1.2 times the largest probability that the oracle finds and a budget of 4,096, and the tests record the status, the hull, and the time of each.  The box of `±1` m/s, whose largest probability lies above `T`, requires verdict 1 with a budget of 64 and at its least budget of 10, and verdict 3 at 9, and the zero burn and the third of the three conjunctions require verdict 1.

## What lies outside the theorems

The theorems concern the model.  The short-encounter assumptions of the conjunction demo, rectilinear relative motion during the encounter, Gaussian position errors constant during it, independent errors, and spherical objects, are not proved, and the line through the state at `t_j` follows the motion only near `t_j`.  The two-body change of the trajectory by the burn neglects perturbations, which enter only through the padding `P`, the caller's premise.  The states, the covariance, the radius, the threshold, the box, and the agreement of frames and epochs are the caller's.  The theorems bound no width: an accepted hull is sound however wide, and a wide one that the budget does not narrow rejects a safe burn with verdict 3.  No theorem states that the search accepts a safe burn for any budget, or that it evaluates every cell before its last evaluation, and the program adds the intervals of the cells left over when it does not.  No theorem states that the burn creates no new conjunction.
