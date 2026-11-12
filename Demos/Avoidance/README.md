# Avoidance maneuver authorizer

[The program](Program.lean) decides whether a proposed impulsive burn may be executed by a spacecraft, the primary, that faces conjunctions with other objects.  It accepts the burn only when a proved upper bound on the two-dimensional probability of collision after the burn lies below a threshold, for every listed conjunction and for every velocity change in a box that models the burn's execution error.  An unproved planner proposes the burn, and the program accepts or rejects it, as the authorizers of [the energy demo](../Energy/README.md) and [the passive-safety demo](../PassiveSafety/README.md) do.  [The theorems](#theorems) state that an accepted burn has, for the model, a probability below the threshold after every velocity change in the box, that the model's trajectories after the burn solve Newton's equation of two-body motion, and that the miss vector is the closest approach of the straight-line relative motion.

`verified_compile` compiles the program, with [the interval layer](../../Library/Numerics/Interval/README.md), the library's `exp`, `erf`, `sin`, and `cos`, and the probability enclosure of [the conjunction demo](../Conjunction/README.md) extended to interval inputs, into a module of 34,225 bytes.  The module agrees with native Lean, bit for bit, on 96 calls, and [the tests](#tests) find the probability of every sampled velocity change inside the returned interval, and the status that each case fixes, in 33 valid inputs and 90 inputs derived from them.  [The requirements](requirements.md) define the model and the interface, and [the review](review.md) records the decisions, the independent review, and the response to each finding.

## Example

The primary is on a circular orbit of radius 6,878.137 km at an inclination of 51.6°, at the x axis at the burn.  A secondary crosses its path 2,700 s later at 90° to its track, with a relative speed of 10.8 km/s, 30 m from the primary's nominal position along the plane's radial axis.  The combined covariance has standard deviations of 0.1, 1, and 0.1 km along the primary's radial, transverse, and normal axes, the hard-body radius is 20 m, and the threshold is `10⁻⁴`.  With 4,096 panels and a zero burn, `authorize` returns status 2 with verdict 1 and the interval `[2.677 × 10⁻³, 2.679 × 10⁻³]`.  A burn of 10 cm/s along the velocity, with a box of `±1` mm/s on each axis about it, returns status 0 with the interval `[0, 3.507 × 10⁻⁶]`, and `authorize_model` then states that the model's probability lies below `10⁻⁴` for every velocity change of the box.  The oracle's largest probability over the box is `1.437 × 10⁻⁶`.  A call takes about 3 ms in Node 24 on a four-core AArch64 virtual machine.

## The model

The primary's state just before the burn is `(r_b, v_b)` at the burn time, and the burn adds `Δv`.  `propagate`, in [the specification](Spec.lean), is the two-body state `t` seconds after a state `(r₀, v₀)`, given by its components, and `stateAt μ r₀ v₀ t` is the same state as two vectors.  The Lagrange coefficients `f` and `g` in the change of the eccentric anomaly give it, with Kepler's equation in the form of SGP4, `E + b cos E − a sin E = ℓ`, whose root the SGP4 and screening demos also use.  [`propagate_newton`](TwoBody.lean) proves by differentiation that the position and velocity of `t ↦ stateAt μ r₀ v₀ t` solve Newton's equation `r'' = −μ r/|r|³` at every time, for a state with `α = 2/|r₀| − |v₀|²/μ > 0` and an eccentricity below 1, and `propagate_zero` that the propagation starts at the state.

Conjunction `j` gives, at its reference time `t_j`, the primary's nominal state `(r₁, v₁)`, the secondary's state `(r₂, v₂)`, the combined covariance `C` in the same inertial frame, and the hard-body radius `R_j`.  The relative state after the burn is the nominal one plus the two-body change that the burn makes, and a displacement `d` within the padding `P`:

`ρ = r₁ − r₂ + (p₁ − p₀) + d`,  `ν = v₁ − v₂ + (u₁ − u₀)`,

with `(p₁, u₁)` and `(p₀, u₀)` the propagations of `(r_b, v_b + Δv)` and `(r_b, v_b)` over `t_j − t_b`.  A zero burn therefore reproduces the message's geometry, and `relative_two_body` states that the model is the two-body trajectory after the burn when the nominal state is the two-body one.  The encounter plane is perpendicular to `ν`, with the axes `x̂` along `r₁ × ν` and `ŷ = ẑ × x̂`, and the miss vector is `m = (ρ · x̂, ρ · ŷ)`.  [`axes_orthonormal`](Geometry.lean) states that the axes are orthonormal and perpendicular to `ν`, and `miss_closest` that `m` is the point of the line `ρ + τ ν` nearest the origin.  The probability after the burn is `Demos.Conjunction.Model.pc` of `m`, the covariance projected on the axes, and `R_j`.

## Interface

```text
authorize  xs : Array Float, N : UInt64  ->  Array Float
pcBox      m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi r : Float, N : UInt64
                                         ->  status, lo, hi

xs[0]             μ (km³/s²), μ > 0
xs[1..3]          r_b (km)
xs[4..6]          v_b (km/s)
xs[7..12]         lx, hx, ly, hy, lz, hz: the box of Δv (km/s), lx ≤ hx, ly ≤ hy, lz ≤ hz
xs[13]            P (km), P ≥ 0
xs[14]            threshold T
xs[15 + 20j]      Δt_j = t_j − t_b (s), Δt_j > 0
xs[16..18 + 20j]  r₁ (km)            xs[19..21 + 20j]  v₁ (km/s)
xs[22..24 + 20j]  r₂ (km)            xs[25..27 + 20j]  v₂ (km/s)
xs[28..33 + 20j]  C_xx, C_xy, C_xz, C_yy, C_yz, C_zz (km²)
xs[34 + 20j]      R_j (km), R_j > 0
N                 panels of each probability enclosure, from 1 to 1,048,576

output   status, K, then for each conjunction j: verdict, lo_j, hi_j

status   0  accepted: every verdict is 0          verdict  0  hi_j < T
         1  invalid input: the output is 1, 0              1  hi_j ≥ T
         2  some verdict is 1, none is 2                   2  the enclosure is rejected, ends 0
         3  some verdict is 2
```

Every value is finite, and the array holds `15 + 20K` values for `1 ≤ K ≤ 64`.  `[lo_j, hi_j]` contains the model's probability for every velocity change of the box and every displacement within the padding.

## Method

The program evaluates the model in interval arithmetic with outward rounding, with the box of velocity changes, the intervals `[−P, P]` of `d`, and every other input as a point interval.  [`enclosure_def`](../../Library/Numerics/Interval/README.md#one-source-for-a-real-function-and-its-interval-program) states each part once, `propagate`, `shape`, `relative`, `axes`, and `project`, and declares the real function, its interval function, and the theorem that the interval function encloses it.

| Part | Computation |
|---|---|
| `keplerRoot` | An approximate root of Kepler's equation in binary64, widened by its residual over the least slope `1 − √(a² + b²)`, with `a² + b²` clamped at zero, since the outward-rounded square of an interval that holds 0 is negative at its lower end and would reject a circular orbit |
| `shape` | `α` and `e²` of the state after the burn and of the nominal state, which the program requires to be shown positive and below 1 |
| `axes` | `x̂`, `ŷ`, `\|r₁ × ν\|²`, and `\|ν\|²`, the last two shown positive |
| `project` | `m` and the covariance projected on the axes in a form centered at the middles of the axes' intervals, `x̂ᵀCx̂ = gᵀCg + 2 (x̂ − g)ᵀCg + (x̂ − g)ᵀC(x̂ − g)`, which keeps a large variance of `C` out of the intervals' widths |
| `pcBoxWith` | The panels of `Demos.Conjunction.pcWith` over `[−R, R]` with the mean and the covariance as intervals |

`project_eq` states that the centered form equals the plain projection, so the centers do not enter the model.  `pcBoxWith`, in [`Demos/Conjunction/Box.lean`](../Conjunction/Box.lean), replaces the setup of `pcWith` with one computed from intervals, and [`pcBoxWith_enclosure`](../Conjunction/BoxSoundness.lean) is proved by `panels_sound_of`, the conjunction demo's proof of the panels for any setup, of which `panels_sound` is the case of the setup of `pcWith`.

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/avoidance/Axioms.lean) reports.  The real value of a float is the real number that it represents, and `val xs i` is the real value of `xs[i]`.  `InBox xs dv` states that the velocity change `dv` lies in the box, and `InPad xs d` that each component of `d` is at most `P` in absolute value.  `encounter xs j dv d` is the model's encounter of conjunction `j`, `pcAfter xs j dv d` its probability, and `Good xs j dv d` the conditions of the model's theorems: `α > 0` and `e² < 1` for both propagated states, `|r₁ × ν|² > 0`, `|ν|² > 0`, a positive definite projected covariance, and `R_j > 0`.

| Code | Theorem | File | Statement |
|---|---|---|---|
| M1 | `propagate_zero` | [TwoBody](TwoBody.lean) | For `μ > 0` and a state `(r, v)` with `α > 0` and `e² < 1`, `stateAt μ r v 0 = (r, v)`. |
| M2 | `propagate_newton`, `root_hasDerivAt` | [TwoBody](TwoBody.lean) | For the same states, the position and velocity of `t ↦ stateAt μ r v t` satisfy `Demos.Orbit.Newton μ`: the position stays away from the origin, its derivative is the velocity, and the velocity's derivative is `−μ r/\|r\|³`, at every real `t`.  The root of `E + b cos E − a sin E = ℓ`, as a function of `ℓ`, has the derivative `(1 − b sin E − a cos E)⁻¹`. |
| M3 | `axes_orthonormal` | [Geometry](Geometry.lean) | For `\|w × ν\|² > 0` and `\|ν\|² > 0`, `x̂` and `ŷ` are unit vectors perpendicular to each other and to `ν`. |
| M4 | `miss_closest` | [Geometry](Geometry.lean) | Under the same hypotheses, `(ρ · x̂)² + (ρ · ŷ)² ≤ \|ρ + τ ν\|²` for every real `τ`, with equality at `τ = −(ρ · ν)/(ν · ν)`. |
| M5 | `relative_two_body` | [Geometry](Geometry.lean) | When the nominal state is `stateAt μ r_b v_b Δt`, the relative state of `relative` is that of `stateAt μ r_b (v_b + Δv) Δt` less the secondary's, plus `d`. |
| | `project_eq` | [Geometry](Geometry.lean) | The centered form of `project` equals the plain projection for every pair of centers. |
| | `keplerRoot.encloses`, `propagate.encloses`, `shape.encloses`, `relative.encloses`, `axes.encloses`, `project.encloses` | [KeplerRoot](KeplerRoot.lean), [Spec](Spec.lean) | Each interval function encloses its real function when its arguments enclose theirs. |
| P1 | `pcBoxWith_enclosure`, `pcBox_enclosure` | [BoxSoundness](../Conjunction/BoxSoundness.lean) | An accepted result has finite ends, and every real point of the five intervals has `c₁₁ > 0`, `c₁₁ c₂₂ − c₁₂² > 0`, and `lo ≤ Model.pc ≤ hi`. |
| A1 | `authorize_sound`, `authorize_model` | [Soundness](Soundness.lean) | When `(authorize xs n)[0]! = 0.0`, `valid xs n` holds, and for every `j < count xs` and all `dv` and `d` with `InBox xs dv` and `InPad xs d`, `Good xs j dv d` and `pcAfter xs j dv d < val xs 14`.  `authorize_model` adds that the trajectories `stateAt μ r_b (v_b + dv)` and `stateAt μ r_b v_b` satisfy `Newton μ` and that the miss vector is the closest approach of the line. |
| A2 | `authorize_enclosure` | [Soundness](Soundness.lean) | For a valid input, `j < count xs`, and an output verdict other than 2, `Good xs j dv d` and `lo_j ≤ pcAfter xs j dv d ≤ hi_j` for the same `dv` and `d`, and verdict 0 gives `pcAfter xs j dv d < val xs 14`. |
| A3 | `authorize_invalid` | [Soundness](Soundness.lean) | `(authorize xs n)[0]! = 1.0` exactly when `valid xs n = false`. |
| | `encounter_eq` | [Soundness](Soundness.lean) | The fields of `encounter xs j dv d` are `ρ · x̂`, `ρ · ŷ`, the covariance projected on `x̂` and `ŷ`, `α` and `e²` of `shape` for both states, `\|r₁ × ν\|²`, and `\|ν\|²`, for the `ρ` and `ν` of `relative`. |
| C1 | `authorize_callSpec`, `avoidance`, `pcBox_call` | [Call](Call.lean) | Function 94, the export `authorize`, returns `authorize xs n` without a trap from every ready store with room for `compiled.authorize.bound (xs, n)` bytes, the module's bytes decode to the module, its start store is ready, and status 0 implies A1.  Function 93, the export `pcBox`, returns the words of `pcBox` without a trap from every ready store, and status 0 implies P1. |
| | `compiled.bytes`, `avoidance_file`, `avoidance_file_decode` | [Compilation](Verified.lean), [file theorems](File.lean) | `encode compiled.module` succeeds with bytes that decode to the module, and `build/verified/avoidance.wasm` holds them. |

The proof of A1 follows the program.  `afterAt_encloses` combines the generated enclosure theorems of `relative`, `shape`, `axes`, and `project`, with `project_eq` for the centers, into the inclusion of the model's encounter in the intervals of `afterAt` for every point of the box and the padding.  `assessOne_sound` reads the conditions of `Good` from the program's tests of the lower and upper ends and applies `pcBoxWith_enclosure`, and `allBelow_spec` collects the conjunctions with `LeanExe.Dialect.loop_induction`.  The proof of M2 differentiates the root of Kepler's equation as the inverse of its left side, with Mathlib's `HasDerivAt.of_local_left_inverse` and `Monotone.continuous_of_surjective`, then the coefficients `f`, `g`, `ḟ`, and `ġ`, and shows that the length of the position is `w/α` by an identity in which `sin² + cos² − 1` appears as an explicit factor.

## Tests

`tests/verified/run.sh --cases avoidance` writes the module, validates it, compares `authorize` and `pcBox` with native Lean on [the module cases](../../tests/TestSupport/Avoidance/Cases.lean), runs [the axiom audit](../../tests/avoidance/Axioms.lean), and checks the file theorems.  The cases are the oracle's inputs of at most 200 values, each at its panel count and at 64 panels, and the oracle's intervals for `pcBox` at 64 and 4,096 panels, 96 calls in all, and the module agrees with native Lean on every one, bit for bit.

[The oracle](../../tests/avoidance/oracle.py) checks the module against the model, computed apart from the program.  It propagates each state from its classical elements with Kepler's equation `E − e sin E = M` solved at 40 digits in mpmath, which agrees with a Runge–Kutta integration of Newton's equation to `8.6 × 10⁻¹⁰` km over 5,400 s, and it takes the axes of the encounter plane from the coordinate axis least aligned with `ν`, which differ from the program's.  It computes the probability as an integral over the angle of the closed-form radial integral along each ray from the disk's center, by the trapezoid rule, which agrees with mpmath's two-dimensional quadrature to `2.8 × 10⁻²¹` relative.  For each conjunction it samples the corners of the box with corners of the padding, the center, and six random points, and climbs from the largest sample by a compass search.  [The requirements](requirements.md#tests) list the checks, among them the containment of every sample in `[lo_j, hi_j]`, the consistency of the statuses with the verdicts and of the verdicts with `hi_j` and `T`, and the status and verdicts that each case fixes in advance.

```sh
uv run tests/avoidance/oracle.py build/verified/avoidance.wasm --mutate
```

All 139 checks pass: 33 valid inputs, 12 invalid ones, 90 inputs whose threshold the oracle sets to `hi_j`, the next double above it, or a value between `lo_j` and `hi_j`, and 4 calls of `pcBox`.  The mutation run alters 95 outputs, and the checks reject all 95.  The reviewer's model of the requirements, with each of its wrong programs as a variant, ran through the same checks, and [the review](review.md#wrong-programs) lists the cases that detect each.

The table gives the ratio of `hi_j` to the largest probability that the oracle finds over the box and the padding, with 4,096 panels.

| Input | Largest probability | `hi_j` | Ratio |
|---|---|---|---|
| Point box near the trajectory after the burn, each kind of orbit | `2.68 × 10⁻³` | `2.68 × 10⁻³` | 1.00 |
| Box of `±1` mm/s, 2,700 s after the burn | `1.44 × 10⁻⁶` | `3.51 × 10⁻⁶` | 2.44 |
| The same, equatorial and polar primaries, 2,000 s | `2.35 × 10⁻⁵` | `5.36 × 10⁻⁵` | 2.28 |
| Box of `±1` mm/s, a day after the burn | `3.38 × 10⁻⁸` | `1.80 × 10⁻⁶` | 53 |
| Box of `±1` cm/s, 2,700 s | `8.29 × 10⁻⁶` | `9.94 × 10⁻⁴` | 120 |
| Box of `±1` m/s, 2,700 s | `2.75 × 10⁻³` | `2.26 × 10⁻²` | 8.2 |
| 10 km cross-track deviation, `±1` mm/s, 8,000 s | `9.7 × 10⁻¹⁵` | `9.2 × 10⁻¹²` | 949 |
| 10 km cross-track deviation, `±1` mm/s, a day | `2.2 × 10⁻⁹` | `1.04 × 10⁻⁴` | `4.7 × 10⁴` |

The width comes from the box: `hi_j` changes from `3.543 × 10⁻⁶` at 64 panels to `3.506 × 10⁻⁶` at 2²⁰ panels for the second row.  The interval of the miss vector is the projection of a box of relative positions, and when the burn's effect lies along a direction oblique to the axes the box holds positions far from the true range, which grows with the time from the burn and the size of the box.  The last row's safe burn therefore gets status 2.  The natural interval form of `x̂ᵀ C x̂` gives status 3 for the same input, since it does not show the conditional variance positive, and `hi_j = 4.4 × 10⁻¹⁰` at 8,000 s.

A call costs `K` evaluations of `pcBoxWith` with `N` panels.  With one conjunction, a call took 1.1 ms at 64 panels, 50 ms at 65,536, and 0.71 s at 2²⁰, and with 64 conjunctions at 4,096 panels it took 178 ms, so the largest input, 64 conjunctions at 2²⁰ panels, takes about 46 s at that rate.

## Limits of the theorems

The theorems concern the model.  The short-encounter assumptions of the conjunction demo, rectilinear relative motion during the encounter, Gaussian position errors constant during it, independent errors, and spherical objects, are not proved.  The burn moves the time of closest approach by `τ* = −(ρ · ν)/(ν · ν)`, and the straight line through the state at `t_j` follows the two-body motion only near `t_j`: the review found the two within 7 mm for `|τ*|` up to 5 s at 10 and 1 km/s, and 4.2 m and a factor of 2.4 in the probability at 10 km/s with `τ* = 26` s.  No input bounds `τ*`.  The two-body change of the trajectory neglects perturbations, which enter only through the padding `P` of the position, and the relative velocity is the model's.  The states, the covariance, the radius, the threshold, the box, and the agreement of frames and epochs are the caller's.

The theorems bound no width.  A program that rejects every burn satisfies them, and the tests check the statuses that the cases fix.  The miss vector's interval is the projection of a box of relative positions, which overestimates the true range when the burn's effect lies along a direction oblique to the axes, and a day after the burn the review measured a range of 1 km for a true range of 5 m.  A subdivision of the box of velocity changes would narrow it.  No theorem states that the burn creates no new conjunction, with the listed secondaries at other times or with other objects.  The module has no C translation or AArch64 image.  The theorems rest on the verified compiler's trusted base, which [the trusted-base document](../../docs/trusted-base.md) describes.

## References

- [Avoidance maneuver authorizer requirements](requirements.md)
- [Avoidance maneuver authorizer: decisions and review](review.md)
- [D. T. Hall, Implementation Recommendations and Usage Boundaries for the Two-Dimensional Probability of Collision Calculation, AAS 19-632, 2019](https://ntrs.nasa.gov/citations/20190028900)
