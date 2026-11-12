# Avoidance maneuver authorizer: decisions and review

[The requirements](requirements.md) specify the authorizer of brief 3.2 of the space-operations candidates.  This record gives each decision with its reason, the findings of the independent reviews of the requirements, and the response to each.

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
| Target | A ground program in WebAssembly | The burn is planned on the ground, and the cost is that of `K` calls of the probability enclosure for each cell. |
| Narrowing the miss vector's interval | A subdivision of the box of velocity changes for each conjunction | Finding 7 below.  A mean-value form would need an enclosure of the derivative of the propagation.  The subdivision reuses the evaluation over a box unchanged, and its soundness needs only that the cells cover the box. |
| Order of the search | A queue of cells in an append-only array with the index of the next cell, in a `LeanExe.repeatWhile` | A budget per split needs a running count of splits, which the step of `Demos.Screening.loop_cover`, the screening and geolocation searches' level-by-level loop, cannot keep, and a level copies every kept cell.  A stack needs the erasure of its last element and refines one region before the others.  The queue evaluates the cells in breadth-first order with constant work for each, and its invariant needs only the lemmas about `push`. |
| Split rule | The longest side at the screening demo's `middle` | With the earlier program as the cell evaluator, an octree split took 10 to 45 % fewer evaluations than a longest-side split when each split cell had a probe, and the difference came from the probes.  With a probe at every third depth the longest side took 257, 443, and 1,065 evaluations where the octree took 235, 469, and 1,009, for thresholds at 1.2 and 2 times the largest probability. |
| Budget | A third argument `S`, the splits of each conjunction's search, from 0 to the cap of the interface | The cost grows with `S`, and only the caller knows its time.  `S = 0` evaluates the box once.  A fixed cap leaves the cost to the program, and a value in the array's header shifts every block's indices.  The statements of `authorize_sound`, `authorize_enclosure`, `authorize_invalid`, `authorize_model`, `authorize_callSpec`, and `avoidance` gain the argument and are otherwise unchanged. |
| Iteration bound | `2S + 1` evaluations of cells, the fuel of the loop | `S` splits append `2S` cells to the first.  Each cell carries the interval of the cell that it was split from, so a search that stops at any step leaves a sound hull, and no theorem about finishing is needed. |
| Unfinished search | Verdict 3 and status 4 | Verdict 1 means that an interval reached the threshold, which A4 states, and verdict 3 that the search ended undecided.  Status 3 keeps precedence over status 2, and status 2 over status 4. |
| Unsafe burns | The probe, an evaluation at the cell's center with no displacement, at every third depth | A cell's own lower end reaches the threshold only over a cell on which the probability varies little.  With the earlier program as the cell evaluator, 4,096 splits of the box of `±1` m/s never showed it, while a probe at each split cell showed it in 25 evaluations and a probe at every third depth in 19.  The probe's center is the witness of A4. |

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
| 7. The miss interval, the projection of a box of relative positions, is much wider than the true range. | Gap | Adopted in [the search over the box](requirements.md#the-search-over-the-box).  In the oracle's case with a box of `±10⁻⁵` km/s 2,700 s before the encounter, the whole box gives `hi = 9.94 × 10⁻⁴` against a largest probability of `8.3 × 10⁻⁶`, and 13 splits give `hi = 8.08 × 10⁻⁵`, below `T = 10⁻⁴`.  The second review below covers the search. |
| 8. The departure from the request's reuse of the screening demo's model and isolation is not recorded. | Gap | Adopted in the decisions above, with the reviewer's measurements. |
| 9. Nothing bounds the shift of the time of closest approach. | Gap | Adopted as a limit with the review's measurements.  An input bound on `−ρ · ν / ν · ν` is open: it needs a new input, which changes the layout of the array, and a new condition of `Good`, which changes the model's statement in A1, A2, and A4.  The search narrows the interval of `τ*` as it narrows the miss vector, so a test of each cell would be effective. |
| 10. The reason for leaving out new conjunctions with the listed secondaries is wrong: that is pairwise screening. | Gap | Adopted.  The requirements give the reason: pairwise screening of the trajectory after the burn needs its isolation over a box of states, which the screening demo's element form does not enclose. |
| 11. The padding covers the position only. | Gap | Adopted as a premise: the relative velocity is the model's.  A padding of `ν` is open: it needs a new input and a change of `relative`, and the search, which splits velocity changes and not a velocity padding, would not narrow the intervals that it widens. |
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
## Review of the search

A second fresh agent reviewed the section "The search over the box", the budget `S`, verdict 3 and status 4, theorem A4, and the tests of the search, with [the method of independent review](../../VKB/entries/independent-review/README.md).  It received the request and the requirements and none of the author's reasoning or program.  Its model computes `authorize(xs, N, S)` from the requirements, evaluating each cell and each probe with the module before the search, whose `authorize` evaluates one interval over the box it is given.  At `S = 0` the model reproduced that module's ends on all 45 cases of the oracle.  It ran the model on the oracle's cases at the named budgets, over 269 searches in which no conjunction used more than `2S + 1` evaluations, `S` splits, or `S` probes, and wrote 32 wrong programs.

| Finding | Severity | Response |
|---|---|---|
| 1. Neither the theorems nor the described tests fix most of the search: 14 of the 32 wrong programs passed every described test, and 7 of them returned the model's output bit for bit on every case, since the output holds only the status, the verdicts, and the hulls. | Gap | Adopted in two of its three parts.  The oracle replays the search with the module's own evaluations of cells and probes, calls with `S = 0`, and requires the output bit for bit, and the cases hold the reviewer's inputs that separate a round-robin split, no split of rejected cells, step 1 with `hi ≤ T`, and the probes over or beside the padding.  A Lean definition of the search beside the program would restate the program, which `authorize_callSpec` ties to the module, so the section's steps and the replay carry the specification of the search. |
| 2. A probe that stops the search with a rejected `r` gives verdict 2 to a conjunction shown at or above `T`: with the relative velocity along `r₁`, the probe gives `[1.4962 × 10⁻³, 1.4972 × 10⁻³]`, and the output is status 3. | Gap | Declined.  The probe's interval holds only at the center, so the hull must take `r`, and verdict 1 with a rejected hull would need A2's containment restricted to accepted hulls.  The burn is rejected with status 3 either way, and the requirements state the rule.  The case with the zero burn and the relative velocity along `r₁` tests the rejection of `\|x\|` at every budget. |
| 3. A probe runs only before a split, so a point box with padding never gets one: the zero burn with a padding of 100 m gives verdict 3 at every budget, while the evaluation at `d = 0` gives 27 `T`. | Gap | Adopted.  While splits remain, the probe applies to every cell that steps 1 and 2 leave undecided at a depth that is a multiple of 3, and the case requires verdict 1.  A conjunction then costs at most `2S + 1` probes. |
| 4. The named budgets lie far above the least budgets, so a search with `S − 1` splits, step 3 before step 1, or `S + 1` evaluations passes. | Gap | Adopted: the cases hold the least budgets 13, 5, and 10 of the box of `±1` cm/s, the cross-track deviation a day after the burn, and the box of `±1` m/s, and the budgets 12, 4, and 9 below them. |
| 5. The precedence of status 4 over status 2 is untested. | Gap | Adopted: the box of `±1` cm/s with a second conjunction at a miss of 600 m gives verdicts 3 and 1 and status 2 with `S = 1`, and status 4 with `S = 0`. |
| 6. No case has a box with both accepted and rejected cells, so a hull that skips rejected intervals, which is unsound, passes. | Gap | Adopted: the box across the escape speed 60 s before the encounter requires status 3. |
| 7. No theorem concerns status 2. | Gap | Adopted: `authorize_shown` states that status 2 gives a valid input and, for some conjunction, a velocity change of the box at which the probability with no displacement lies at or above `T`. |
| 8. The check of verdict 1 tests neither `d = 0` nor the program's witness. | Gap | Adopted: the replay gives the witness, the lower corner of the cell or the probe's center, and the oracle requires its probability with `d = 0` at or above `T`. |
| 9. Neither the cost nor the memory at the top of the range of `S` is stated: at `2²⁰` one conjunction takes 2,097,153 evaluations, about 2.4 h at 4,096 panels, and the requirements do not relate the allocation bound to `S` or `K`. | Gap | Adopted in part.  The cap of `S` is 65,536, at which a conjunction costs at most 262,146 evaluations, about 13 min at 4,096 panels.  The module releases each search's cells before the next conjunction: with 16 panels, 65,536 splits left its memory at 22 MiB.  No theorem reduces the generated allocation bound to a closed form, and the README states that C1 holds for stores with room for it. |
| 10. The derived thresholds must come from a run at `S = 0`, and the rule for the threshold above `lo` fails when `lo = hi`. | Wording | Adopted: the thresholds come from the call with `S = 0`, and the required verdict is that of a single evaluation, 0 when `hi < T`, 1 when `lo ≥ T`, and 3 otherwise. |
| 11. "It then adds to the hull the intervals of the cells not evaluated" reads as covering only some stops. | Wording | Adopted: "At every stop". |
| 12. "Three splits halve each side of a cube" holds only for cubes, and the probe needs an exact definition. | Wording | Adopted: the sentence names cubes and boxes with unequal sides, and the probe is the interval of the point box at the center with the padding 0. |
| 13. The elongated covariance's largest probability is `2.43 × 10⁻⁴`, while `0.011` is the hull's upper end. | Wording | Adopted. |

## Wrong programs of the search

The reviewer's model, with the probe of finding 3 and the cap of finding 9, ran with each of its wrong programs through the checks of [the oracle](../../tests/avoidance/oracle.py), the replay included, on its cases of at most 200 values other than those with tightened thresholds, the inputs derived from them, and the replay's cases with `S = 1`.  The correct model passed every check.  The table gives the number of cases that detect each variant and some of them.

| Wrong program | Cases that detect it |
|---|---|
| The cells not evaluated add nothing to the hull at a stop | 2: the box of `±1` m/s at budgets 64 and 10 |
| The halves carry a rejected interval | 2: the same |
| A stop does not add the stopping cell's `r` | 62, among them the zero burn and the derived thresholds `T = lo` |
| A split also adds `r` to the hull | 46, among them the replay's cases with `S = 1` |
| The hull skips rejected intervals | 1: the box across the escape speed |
| The probe over the padding | 2: the zero burn with a padding of 100 m and the box about the cancelling burn with that padding |
| The probe at `d = (P, P, P)` | 2: the point burn with a padding of 100 m and the box about the cancelling burn with that padding |
| The probe at the cell's lower corner | 3, among them the box of `±1` m/s |
| A probe at every depth | None |
| No probe | 9, among them the three conjunctions and the box of `±1` m/s |
| A probe at depth 0 only | 2: the box of `±1` m/s at budgets 64 and 10 |
| A probe that stops on `hi ≥ T` | 11, the replay's cases with `S = 1` of point boxes |
| A probe stop with a rejected `r` adds the probe's interval | 1: the relative velocity along `r₁` |
| A split of the shortest side | 43 |
| A split of the side of index depth mod 3 | 4, among them the box with sides of 8, 2, and 2 × 10⁻⁵ km/s |
| Step 4 before step 1 | 24, among them the box of `±1` mm/s |
| No split of a rejected cell | 2: the elongated covariance with the box of `±1` m/s and the relative velocity along `r₁` with `T = 0.1` |
| The middle `(a + b)/2` | None |
| The cells evaluated in depth-first order | 4: the box of `±1` m/s at budgets 64, 10, and 9, and the box of `±1` cm/s at 12 |
| `S + 1` splits | 41, among them the derived thresholds above `lo` |
| `S − 1` splits | 39, among them the replay's cases with `S = 1` |
| At most `2S` evaluations of cells | 54, every call with `S = 0` |
| At most `S + 1` evaluations, the rest dropped | 18 |
| Step 2 with `lo > T` | 45, the derived thresholds `T = lo` |
| Step 1 with `hi ≤ T` | 32, the replay's cases with `S = 1` |
| Verdict 1 for every accepted hull with `hi ≥ T` | 181 |
| A probe stop gives verdict 3 | 8, among them the three conjunctions |
| Status 4 before status 2 | 1: the box of `±1` cm/s with a miss of 600 m and `S = 1` |
| Status 4 before status 3 | 5, the derived thresholds of the case with one rejected and one high conjunction |
| No status 4 | 177 |
| `S = 65,536` invalid | 1: the zero burn with the largest budget |
| `S = 65,537` valid | 1: the budget above the largest |

No case detects two of the variants, since their outputs equal the model's on every case.  A probe at every depth stops the search earlier only when a probe at a depth that is not a multiple of 3 reaches `T` before the next probe at a multiple of 3, and otherwise it changes only the cost.  The middle `(a + b)/2` differs from `a + (b − a) · 0.5` by at most a rounding of the last bit, and on these cases the two forms give the same outputs.
