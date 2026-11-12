# Avoidance maneuver authorizer: decisions and review

[The requirements](requirements.md) specify the authorizer of brief 3.2 of the space-operations candidates.  This record gives each decision with its reason, the findings of the independent review of the requirements, and the response to each.

## Decisions

| Question | Choice | Reason |
|---|---|---|
| Execution error | A box of velocity changes in the inertial frame | The theorem then covers every executed velocity change in the box, with no assumption on its distribution.  An added covariance would need the state transition matrix of the linearized motion, and the theorem would concern that linearization. |
| Propagation of the box of states | The Lagrange coefficients `f` and `g` in the change of the eccentric anomaly, from the state at the burn | Classical elements, which the screening demo's `Orbit` takes, separate the argument of perigee and the mean anomaly, which are ill-conditioned for near-circular orbits and anti-correlated over a box.  For a primary with `e = 0.002` and a box of `±1` mm/s, both spread by `3.2 × 10⁻⁴` rad over the corners.  The true spread of the position after 5,400 s is 36 m, and with the two angles varied independently it is 3.3 km.  The review measured a node that spans 180° for an equatorial primary.  The state form keeps Kepler's equation of the SGP4 demo, `Demos.Sgp4.Kepler.root`, which the screening demo uses. |
| Meaning of the propagation | A theorem that the closed form solves Newton's equation, `Demos.Orbit.Newton` | The passive-safety demo proves its closed form by differentiation.  `Demos.Orbit.Newton` is the orbit-determination demo's definition of two-body motion, so the theorem uses no definition of this demo. |
| The nominal trajectory | The message's states at the reference time plus the two-body change of the trajectory by the burn | A zero burn then reproduces the message's geometry, while a two-body propagation of the whole trajectory over hours differs from the operator's propagator by kilometers.  `relative_two_body` (M5) states that the model is the two-body trajectory after the burn when the nominal state is the two-body one. |
| The closest approach | The straight line through the relative state at the reference time | The two-dimensional model takes the relative motion as rectilinear during the encounter, and the miss vector of the line has a closed form, which `miss_closest` (M4) states.  The screening demo's isolation returns intervals of time within a distance and gives no miss vector or plane.  The review compared the line's miss with the two-body closest approach: they agree to 7 mm, with the probability within `3 × 10⁻⁴` relative, for shifts of the time of closest approach up to 5 s at 10 and 1 km/s. |
| Axes of the encounter plane | `x̂` along `r₁ × ν`, `ŷ = ẑ × x̂` | The axes come from inputs that every case has, and they fail only for a relative velocity parallel to the primary's position.  The axes along the miss vector would fail for a direct hit, the case that most needs a maneuver. |
| Padding | `P` on each component of the relative position | It carries the caller's premise on perturbations of the burn's effect, as the screening demo's padding does. |
| Root of Kepler's equation | `keplerRootI`, `Demos.Sgp4.Kepler.rootI` with the sum `a² + b²` clamped at zero | The outward-rounded square of an interval that holds 0 has the lower end `−4.9 × 10⁻³²⁴`, which `sqrt` rejects, so `rootI` rejects a circular orbit.  Changing `rootI` would change the bytes of the SGP4 module. |
| Probability for interval inputs | `pcBoxWith` in `Demos/Conjunction/Box.lean`, the panels of `pcWith` with an interval setup, and `panels_sound_of`, the proof of `panels_sound` for any setup | `panels_sound` keeps its statement and becomes a corollary, and `pc`, `assess`, and the module `conjunction` do not change. |
| Target | A ground program in WebAssembly | The burn is planned on the ground, and the cost is that of `K` calls of the probability enclosure. |

## Review

A fresh agent reviewed the requirements against brief 3.2, the scope statement, and the plan's sections "Starting point" and "What every design states", with [the method of independent review](../../VKB/entries/independent-review/README.md).  It received none of the author's reasoning.  It built a model of the requirements in Python, real numbers in mpmath at 30 digits and binary64 intervals with every endpoint moved one step outward, and an oracle from classical elements, a closest approach by Gram–Schmidt axes, and a two-dimensional quadrature.  It compared 2,800 propagations, with a largest relative difference of `1.8 × 10⁻²⁵`, checked M1 to M5 numerically, ran 54 cases with 1,593 oracle probabilities, all inside the method's enclosures, and wrote 16 wrong programs.

| Finding | Severity | Response |
|---|---|---|
| 1. A program that rejects every burn passes every described test, since no check fixes a status in advance. | Defect | Adopted.  Each named case fixes its status and verdicts in advance from the oracle's margins, and the cases built to be accepted require status 0. |
| 2. The check of status 2 where a sample exceeds `10 T` contradicts status 3 for a rejected enclosure in the same input. | Defect | Adopted.  The check requires a verdict other than 0. |
| 3. No check ties the verdicts to `hi_j` and `T`, or the status to the verdicts. | Gap | Adopted.  The oracle checks both, and after the first run it builds cases whose threshold equals `hi_j`, the next double above it, and a value between `lo_j` and `hi_j`.  A case holds one rejected and one high conjunction. |
| 4. The described cases cannot detect errors in `Φ` or in the velocity after the burn. | Gap | Adopted.  Point boxes with the secondary near the trajectory after the burn give probabilities near `10⁻²` for each kind of orbit at 600, 8,000, and 86,400 s, and two cases put 5 km of the relative position along `ν`, at 10 and 1 km/s. |
| 5. Sampling the corners and random points misses interior maxima. | Gap | Adopted.  The oracle climbs from the largest sample by a compass search inside the box and the padding. |
| 6. The natural interval form of `x̂ᵀ C x̂` multiplies the variance along `ν` by the width of the axes, so moderate boxes reject. | Gap | Adopted.  `project` computes the covariance in the form centered at the middles of the axes' intervals, an identity over the reals that `project_eq` states.  For the oracle's input with a cross-track deviation of 10 km and a box of `±1` mm/s a day after the burn, the natural form gives status 3 and the centered form verdict 1 with `hi = 1.04 × 10⁻⁴`, and at 8,000 s the natural form gives `hi = 4.4 × 10⁻¹⁰` and the centered form `9.2 × 10⁻¹²`. |
| 7. The miss interval, the projection of a box of relative positions, is much wider than the true range. | Gap | Open.  In the oracle's case with a box of `±10⁻⁵` km/s 2,700 s before the encounter, `hi` is `9.96 × 10⁻⁴` against a largest sampled probability of `8.3 × 10⁻⁶`, so a safe burn gets status 2.  A subdivision of the box, with a bound on the count, would narrow the interval, and a mean-value form would need a derivative of the propagation with an enclosure. |
| 8. The departure from the request's reuse of the screening demo's model and isolation is not recorded. | Gap | Adopted in the decisions above, with the reviewer's measurements. |
| 9. Nothing bounds the shift of the time of closest approach. | Gap | Adopted as a limit with the review's measurements.  An input bound on `−ρ · ν / ν · ν` is open. |
| 10. The reason for leaving out new conjunctions with the listed secondaries is wrong: that is pairwise screening. | Gap | Adopted.  The requirements give the reason: pairwise screening of the trajectory after the burn needs its isolation over a box of states, which the screening demo's element form does not enclose. |
| 11. The padding covers the position only. | Gap | Adopted as a premise: the relative velocity is the model's. |
| 12. "A covariance that is not positive definite" is ambiguous. | Gap | Adopted.  The cases hold a negative definite covariance, rejected, and a covariance indefinite along `ν` whose projection is positive definite. |
| 13. No theorem for status 1, A2 omits the conditions, C1's statement is loose, and a program that rejects everything satisfies the theorems. | Gap | Adopted: `authorize_invalid`, `Good` in `authorize_enclosure`, one call theorem for each export, and a sentence in the limits. |
| 14. No cost bound. | Gap | Adopted: the requirements state the cost per conjunction and the time measured in the tests. |
| 15. Wording: `n` names the mean motion and the panel count, the planner's nominal burn is no input, `pcBox`'s interface is incomplete, and the clamped root needs its own name. | Wording | Adopted. |

## Wrong programs

The reviewer's model computes the output of the interface and carries each wrong program as a variant.  After the revision, the variants ran through the checks of [the oracle](../../tests/avoidance/oracle.py) on its 42 cases of at most 200 values, at 1,024 panels, with the oracle's samples and compass search, and the correct model passed every check.  The table gives the cases that detect each variant.

| Wrong program | Cases that detect it |
|---|---|
| `b_k` with its sign flipped | The point boxes at 8,000 and 86,400 s from a low orbit with `e = 0.01`, from the equatorial orbit, and from the orbit with `e = 0.3`, and the two with 5 km along `ν` |
| `ḟ` with its sign flipped, or `u₀ − u₁` in place of `u₁ − u₀` | The two point boxes with 5 km along `ν` |
| `ġ` with `R₀α` in place of `w`, or the plane from the nominal `ν` | The point box with 5 km along `ν` at 1 km/s |
| `p₀ − p₁` in place of `p₁ − p₀` | 14 cases, among them the point boxes and the three conjunctions |
| The padding added after the projection | The point box with a padding of 100 m |
| The padding ignored | Both cases with padding |
| `c₁₂` dropped | The point boxes a day after the burn and from the orbit with `e = 0.3` |
| The box evaluated at its center only | 16 cases |
| The box evaluated at its corners only | 5 cases, among them the box about the burn that cancels the miss |
| `rootI` without the clamp | 13 cases, through their fixed statuses |
| The verdict `lo < T` | 5 cases, among them the three conjunctions |
| Status 0 despite a rejection | The four cases with a rejected enclosure |
| Status 2 before status 3 | The case with one rejected and one high conjunction |
| Every burn rejected with verdict 1 | 15 cases, among them every case whose status is fixed at 0 |
| The verdict `hi ≤ T` | The derived cases with `T = hi`, which require verdict 1, by construction.  The run of the variants did not build them. |
| `g` in the form with the time difference | None: it computes the same real function with wider intervals |
