# Passive safety: a proved check of relative orbits with missed burns

[The program](Program.lean) decides whether a plan of impulsive burns for a deputy spacecraft near a chief in a circular orbit keeps a minimum separation from the chief, under the Hill–Clohessy–Wiltshire model, when every burn executes and when any one burn is missed.  It takes a box of initial relative states, which covers the navigation error, and a box of velocity changes for each burn, which covers the execution error.  It returns a lower bound on the separation over a horizon and a lower bound on the distance in the radial and cross-track plane for all time after each scenario's last burn, and it accepts the plan only when both bounds meet their thresholds.  Its searches refine past the thresholds until each bound lies within a target accuracy, an input, of the least bound that they find at a single time, and between burns they enclose each panel by a second-order Taylor form.  An unproved planner proposes the plan, and the program accepts or rejects it, as the authorizer of [the energy demo](../Energy/README.md) does.  [The soundness theorem](Soundness.lean) `check_sound` states what an accepted result implies for every trajectory of the model from the boxes.

[`verified_compile`](Verified.lean) compiles the program, with the library's `sin` and `cos` and [the interval layer](../../Library/Numerics/Interval/README.md), into a module of 24,897 bytes.  In Wasmtime, the module's `check` export agrees with native Lean, bit for bit, on 57 cases, and [the integration test](#tests) finds every bound of the accepted cases below the minima of trajectories that a numerical integration samples from the boxes.  [The requirements](requirements.md) specify the program, and [the review](review.md) records the decisions and two independent reviews, of the requirements and of the panel enclosure and the accuracy.

## The model

The frame is the chief's local-vertical, local-horizontal frame: `x` points radially outward, `y` along the chief's velocity, and `z` along the orbit normal.  For a chief in a circular orbit of mean motion `n`, the Hill–Clohessy–Wiltshire equations are

`ẍ = 3n²x + 2nẏ`,  `ÿ = −2nẋ`,  `z̈ = −n²z`.

[The model](Model.lean) takes their closed-form solution as its definition: `Model.flow n τ s` is the state at time `τ` from the state `s` at time 0, with `θ = nτ`,

| Component | Value |
|---|---|
| `x(τ)` | `(4 − 3 cos θ) x + (sin θ / n) vx + (2/n)(1 − cos θ) vy` |
| `y(τ)` | `6(sin θ − θ) x + y − (2/n)(1 − cos θ) vx + ((4 sin θ − 3θ)/n) vy` |
| `z(τ)` | `cos θ z + (sin θ / n) vz` |

and the velocities that are their derivatives.  `flow_hasDerivAt` proves by differentiation that the six components satisfy the first-order system `x' = vx`, `y' = vy`, `z' = vz`, `vx' = 3n²x + 2n vy`, `vy' = −2n vx`, `vz' = −n²z`, `flow_zero` that the closed form starts at `s`, and `flow_unique` that every solution with the value `s` at 0 equals it, by Mathlib's uniqueness theorem for differential equations with a Lipschitz right-hand side, `ODE_solution_unique_univ`.  `flow_add` follows from uniqueness: the closed form over `a + b` is the closed form over `a` after the closed form over `b`.

A burn changes the velocity at its time and leaves the position unchanged.  `Model.path n t₀ s bs t` executes the burns of the list `bs` in order from the state `s` at `t₀`, and `path_eq` writes the result, for burns in nondecreasing order of time, as the closed form from the initial state plus the closed form of each earlier burn's velocity change.  `Model.select N j bs` gives the burns of scenario `j` of a plan of `N` burns:

| Scenario | Burns that execute |
|---|---|
| `0` | All |
| `k`, for `1 ≤ k ≤ N` | All but burn `k` |
| `N + k`, for `1 ≤ k ≤ N` | Burns `1` to `k − 1`, after which the deputy drifts |

Scenarios `1` to `N` model a missed burn after which the later burns execute, and scenarios `N + 1` to `2N` model the free drift after a failure, which passive safety concerns in Fehse's account.  Scenario `N + 1` is the initial orbit, and scenario `2N` repeats scenario `N`.  The theorems name the times after a scenario's last burn as the times `t ≥ 0` at or after every burn of `Model.select N j bs`.

## Interface

```text
check  xs : Array Float, fuel : UInt64, acc : Float  ->  status, scenario, stop, sep, rc

xs[0]          n        mean motion of the chief, n > 0
xs[1]          T        horizon, T > 0
xs[2]          dmin     separation threshold, dmin ≥ 0
xs[3]          drc      threshold of the radial and cross-track distance, drc ≥ 0
xs[4] to [15]           lower and upper ends of x, y, z, vx, vy, vz at time 0
xs[16 + 7(k−1)]         time of burn k, 0 ≤ t₁ ≤ … ≤ t_N ≤ T
xs[17 + 7(k−1)] to [22 + 7(k−1)]   lower and upper ends of Δvx, then of Δvy, then of Δvz
fuel           panels that each search may evaluate, 1 to 1,048,576
acc            target accuracy of the bounds, a length, acc ≥ 0

status  0  accepted
        1  the size is not 16 + 7N with N ≤ 16, or the fuel or the accuracy is out of range
        2  a value is not finite or is out of range or order
        3  a separation search did not show dmin at its smallest panel
        4  a radial and cross-track search did not show drc at its smallest panel
        5  a separation search used its fuel
        6  a radial and cross-track search used its fuel
        7  an interval operation rejected, or a panel's midpoint lies outside the panel
```

Every quantity uses one unit of length and one unit of time, with `n` in radians per unit of time.  A status from 3 to 7 names the scenario of the failed search in `scenario` and, in `stop`, the start of its last panel, a time for the separation search and a phase for the radial and cross-track search.  Statuses 3 and 4 include plans that violate a threshold and plans whose bounds are too conservative to show that they meet it.  On acceptance, `sep` is the larger of `dmin` and the rounded-down square root of the least lower end of the separation searches' panels, and `rc` the same for `drc`.

For the safety ellipse of radial and cross-track amplitude 100 m about a chief of mean motion 0.0011313 rad/s, with the box `±1` m in position and `±10⁻⁴` m/s in velocity, a day as the horizon, both thresholds at 50 m, a fuel of 100,000 panels, and an accuracy of 0.1 m, `check` returns status 0 with `sep = 92.491` and `rc = 92.496` after 1,526 panels.  The sampled minimum of both distances over the box is 92.59 m.  With an accuracy of `1e300` the thresholds alone decide each panel, and the bounds are 50.06 m and 61.05 m after 428 panels, and with an accuracy of 0.01 m they are 92.580 m and 92.581 m after 2,634 panels.  The same input with `drc = 150` returns status 4 at scenario 0.

## Method

The closed form is linear in the state and composes over time, so the position of a scenario's trajectory at `t` is

`p(t) = P(t) s₀ + Σ over executed burns k of P(max(t − t_k, 0)) Δv_k`,

with `P(τ)` the position part of the closed form, and `P(0) Δv = 0`.  [The interval forms](Closed.lean) of the closed form and of the Taylor forms below come from `enclosure_def`, which declares each real function, its interval function, and the theorem that the interval function encloses it.  `positionI` evaluates the formula with the box of initial states, the boxes of the velocity changes, and an interval of time, and `velocityI` evaluates the velocity of the same terms.

`sepSearch` covers `[0, T]` with panels from 0.  A panel extends the covered part when the lower end `ℓ` of its interval of the squared separation lies at or above an upper bound of `dmin²` and either `√ℓ` lies within the accuracy of a record `M`, `ℓ ≥ (√M − acc)²`, or the panel has the smallest step, `T·2⁻⁴⁰`, and the step then doubles up to `T`.  Another panel halves the step, and a panel at the smallest step that fails its threshold ends the search with status 3.  `M` is the least lower end of the squared distance at the midpoints of the panels that the searches of the same kind have evaluated, in this scenario and the ones before it, so every accepted panel above the smallest step lies within `acc` of the final `M`, and so does the bound that the program returns.  `nonneg` clamps each squared distance to its part at or above 0, since outward rounding moves an exact 0 below 0, and the bound of a zero threshold is 0, so a zero threshold accepts every panel that the accuracy accepts.

Between burns the trajectory is smooth.  On a panel with no burn time of the scenario strictly inside it, `smoothSep` and `smoothRc` evaluate the second-order Taylor form of the squared distance `g` about the panel's midpoint `t_m`, `g(t_m) + g'(t_m)(t − t_m) + g''(ξ)(t − t_m)²/2`, with `g' = 2 p·v` and `g'' = 2(|v|² + p·a)` for the acceleration `a` of the equations.  The values at `t_m` come from `positionI` and `velocityI` at the midpoint, where the formula is exact up to rounding for every state of the boxes, and the values at `ξ` from `velocityI` over the panel and the mean-value form `p(t_m) + v(T)(T − t_m)` of the position.  The radial and cross-track interval is the intersection of the Taylor form of `x² + z²` with the squares of the components over the panel, and the separation's interval is the intersection of the Taylor form of `x² + y² + z²` with the radial and cross-track interval plus the square of `y`.  The second intersection removes the spread of `y·vy` over a box whose along-track position drifts by hundreds of meters, as the safety ellipse's box does in a day.  A separation panel that contains a burn time, where the velocity jumps, takes the natural interval form of `positionI` over the panel.

The radial and cross-track components of every closed-form trajectory depend on time only through `sin nτ` and `cos nτ`, drifting along the track or not, and `Model.flow_phase` states it.  `rcSearch` therefore covers one period after the scenario's last burn `t_L`: it evaluates the position formula at the times `t_L + φ/n` for the phases `φ` of `[0, 2π]`, with the same steps, against `drc²`.  For a point state in bounded relative motion, the minimum over the phase is the minimum radial and cross-track separation of the relative eccentricity and inclination vectors of D'Amico and Montenbruck, and `rc` bounds that minimum over the box from below.

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/passivesafety/Axioms.lean) reports, and the theorems about `check xs fuel acc` hold for every `fuel` and `acc`.  The real value of a float is the real number that it represents, and `val xs i` is the real value of `xs[i]`.  `InBox xs s` states that the state `s` lies in the box of initial states, and `Plan xs bs` that the list `bs` has one burn for each group of seven values, at the plan's time, with each velocity change in the plan's interval.

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `Model.flow_hasDerivAt` | [`Model.lean`](Model.lean) | `n ≠ 0` | The six components of `t ↦ flow n t s` have at every `τ` the derivatives of the first-order system `x' = vx`, `y' = vy`, `z' = vz`, `vx' = 3n²x + 2n vy`, `vy' = −2n vx`, `vz' = −n²z`. |
| `Model.flow_zero` | [`Model.lean`](Model.lean) | None | `flow n 0 s = s`. |
| `Model.flow_unique` | [`Model.lean`](Model.lean) | `n ≠ 0`, a function that satisfies the system at every time with the value `s` at 0 | The function equals `t ↦ flow n t s`. |
| `Model.flow_add` | [`Model.lean`](Model.lean) | `n ≠ 0` | `flow n (a + b) s = flow n a (flow n b s)`. |
| `Model.path_eq` | [`Model.lean`](Model.lean) | `n ≠ 0`, burns in nondecreasing order of time | `path n t₀ s bs t` is the closed form from `s` plus the closed forms of the velocity changes of the burns at or before `t`. |
| `Model.flow_phase` | [`Model.lean`](Model.lean) | `n ≠ 0` | Every `τ` has a `φ` in `[0, 2π)` at which the radial and cross-track components of `flow n (φ/n) s` equal those of `flow n τ s`. |
| `Model.taylor_two` | [`Smooth.lean`](Smooth.lean) | `f` has the derivative `f1` and `f1` the derivative `f2` at every point | `f t = f m + f1 m (t − m) + f2 ξ (t − m)²/2` for some `ξ` between `m` and `t`. |
| `Model.smooth_motion` | [`Smooth.lean`](Smooth.lean) | `n ≠ 0` | The closed form from `s` plus the closed forms of the burns of a scenario at or before a time `S` satisfies the first-order system at every time. |
| `check_input` | [`Soundness.lean`](Soundness.lean) | `xs.size < 2^64`, `check` returns status 0 | The array holds `16 + 7N` values with `N ≤ 16`, some state lies in the box, some list of burns matches the plan, and every matching list is in nondecreasing order of time in `[0, T]`. |
| `check_sound` | [`Soundness.lean`](Soundness.lean) | `xs.size < 2^64`, `check` returns status 0 | `n > 0`, `T > 0`, `dmin ≥ 0`, `drc ≥ 0`, `dmin ≤ sep`, and `drc ≤ rc`.  For every `s` with `InBox xs s`, every `bs` with `Plan xs bs`, and every scenario `j ≤ 2N`, the separation of `path n 0 s (select N j bs)` at every `t` in `[0, T]` is at least `sep`, and its radial and cross-track distance at every `t ≥ 0` at or after every burn of the scenario is at least `rc`. |
| `check_passive` | [`Soundness.lean`](Soundness.lean) | `xs.size < 2^64`, `check` returns status 0 | For the same states, burns, and scenarios, the separation at every `t ≥ 0` is at least `min dmin drc`. |
| `compiled.check.implements` | [`Verified.lean`](Verified.lean) | A heap with the allocator invariant, a store that holds the tables of `sin` and `cos`, and argument words that represent the arguments | The export `check` returns the words of `check xs fuel acc` without a trap. |
| `compiled.check.native` | [`Verified.lean`](Verified.lean) | A C global environment that holds the translation's globals, memory, and functions, and the premises of `compiled.check.implements` | The C translation's `check` computes `check xs fuel acc` as `compiled.check.implements` states. |
| `check_call`, `passive_safety` | [`Call.lean`](Call.lean) | A ready store | The module's bytes decode to the module, whose export `check`, function 86, returns `check xs fuel acc` without a trap from every ready store, and every accepted result meets `check_passive`. |
| `passivesafety_file`, `passivesafety_file_decode` | [`File.lean`](File.lean) | `build/verified/passivesafety.wasm` as written | The file holds `encode compiled.module` and decodes to `compiled.module`. |

The proof of `check_sound` follows the program.  `positionI_encloses` encloses the position formula from the loop over the burns, `path_position` equates the formula with the model's trajectory through `Model.path_eq` and `Model.kicks_selectFrom`, and `path_smooth` equates it on a panel without a burn time inside with `Model.smooth`, whose derivatives `Model.smooth_motion` states.  `smooth_panel` applies `Model.taylor_two` and the mean value theorem to the squared distances of `Model.smooth`, and `sepPanel_encloses` and `rcPanel_encloses` cover both forms of a panel.  `search_covered` states that every search covers its finished part with bounds of the function that its panels enclose, whatever its accuracy, since a panel extends the covered part only when its lower end meets the threshold.  `rc_good` reduces every time after a scenario's last burn to the period that the search covers, by `Model.flow_phase` and `Model.path_after`, and `scan_sound` collects the scenarios.

## Tests

`tests/verified/run.sh --cases passivesafety` writes the module, validates it, compares `check` with native Lean on [the cases](../../tests/TestSupport/PassiveSafety/Cases.lean), runs [the axiom audit](../../tests/passivesafety/Axioms.lean), and checks the file theorems.  All 57 cases agree bit for bit.  The cases fix the status and the scenario of each result: accepted plans, rejections with each status, the plans of the review of the requirements with burns at generic phases and nonzero components, and the plans of the review of the accuracy, which detect the wrong programs that [the review](review.md) lists.

[`tests/passivesafety/run.sh`](../../tests/passivesafety/run.sh) runs the integration test.  [The oracle](../../tests/passivesafety/reference.py) integrates the equations with a fixed-step fourth-order Runge–Kutta method in double precision, independent of the closed form, which it first compares with the integration over three orbits from 40 random states, with a largest relative difference of 7.2e-13.  For each case it requires the expected status and scenario.  For each accepted case it integrates every scenario from the 64 corners of the box of initial states and 200 random states in it, with velocity changes from the corners and the interiors of the burns' boxes, samples each coast 4,000 times a period and refines around each sample's minimum, and requires the sampled minima of the separation and of the radial and cross-track distance to be at least `sep` and `rc`.  It also integrates the state from the centres of the boxes with the change from each input's half-width, computes the componentwise bound, the least distance of the box that holds each component's values over the boxes, and requires `sep` and `rc` to lie within `acc`, plus a millionth, of it.  For each rejection with status 3 or 4 it integrates the named scenario from the same samples, and in every such case a sample violates the threshold.

| Case | Plan | `acc` | Status, scenario | `sep`, componentwise, sampled | `rc`, componentwise, sampled | Panels |
|---|---|---|---|---|---|---|
| `ellipse` | Safety ellipse, one day | 0.1 | 0 | 92.49, 92.59, 92.59 | 92.50, 92.59, 92.59 | 1,526 |
| `ellipseCoarse` | The same, the thresholds alone | `1e300` | 0 | 50.06, 92.59, 92.59 | 61.05, 92.59, 92.59 | 428 |
| `ellipseFine` | The same | 0.01 | 0 | 92.580, 92.590, 92.590 | 92.581, 92.590, 92.590 | 2,634 |
| `vbarHold` | Hold 200 m behind the chief, `drc = 0` | 0.1 | 0 | 200.00, 200.00, 200.00 | 0, 0, 0 | 2 |
| `vbarLateBurn` | The same hold for 6,000 s with a burn of 1 m/s along the track at 5,900 s | 0.1 | 0 | 101.48, 101.48, 101.48 | 0, 0, 0 | 98 |
| `hopShort` | Tangential hop of 100 m with a stop burn, 1.5 orbits | 0.1 | 0 | 54.31, 54.32, 54.32 | 0, 0, 0 | 125 |
| `hopLong` | The same over 3 orbits: the drift after a missed stop burn reaches the chief | 0.1 | 3, scenario 2 | | | 169 |
| `radialHop` | Radial hop from 200 m to 100 m behind, 2 orbits, `±0.1` m | 0.1 | 0 | 91.36, 91.41, 91.41 | 0, 0, 0 | 178 |
| `radialHopWide` | The same over 4 orbits with `±0.5` m: the radial error drifts the deputy to 22 m | 0.1 | 3, scenario 0 | | | 233 |
| `geoEllipse` | Safety ellipse of 1 km about a geostationary chief, 2 days | 0.1 | 0 | 923.83, 923.91, 923.91 | 923.83, 923.91, 923.91 | 431 |
| `formation` | Bounded orbit of radial amplitude 100 m and cross-track amplitude 200 m, 2 orbits | 0.1 | 0 | 92.58, 92.63, 93.37 | 92.58, 92.63, 92.63 | 151 |
| `acceptBurns` | Along-track burns one and 1.5 orbits after the start, 4 orbits | 0.1 | 0 | 558.74, 558.74, 558.78 | 22.10, 22.17, 22.18 | 785 |
| `genericK3` | Two burns at generic phases, every component nonzero | 0.1 | 0 | 12.06, 12.12, 12.20 | 8.18, 8.27, 8.28 | 501 |
| `random34` | A point state and two burns of the review's random search | 0.1 | 0 | 157.70, 157.77, 157.77 | 1.13, 1.17, 1.17 | 344 |
| `missedDrift` | A drift stopped by one burn; the missed burn passes within 33 m | 0.1 | 3, scenario 1 | | | 1,396 |
| `freeDrift` | Two stop burns; only the free drift after a missed first burn passes within 33 m | 0.1 | 3, scenario 3 | | | 1,621 |
| `genericL` | Two burns at generic phases; the radial and cross-track distance falls to 5.22 m after the plan without burn 1 | 0.1 | 4, scenario 1 | | | 431 |
| `flyByTurn` | A pass along the track of a geostationary chief with a turning burn at 400 s that comes within 60 m | 0.1 | 3, scenario 0 | | | 87 |
| `accZero` | `formation` with accuracy 0 | 0 | 5, scenario 0 | | | 100,000 |

The componentwise bound lies below the sampled minimum where the box of each component's values at one time holds positions that no trajectory from the boxes reaches together.  For `formation` the radial position is least when the along-track position is far from 0, but the box of the components holds both at once, so `sep` lies 0.79 m below the minimum of 93.37 m with an accuracy of 0.1 m.  The cases of statuses 1, 2, 5, 6, and 7 cover a short array, an array of more than 16 burns, fuel of 0 and above the limit, an accuracy that is negative, NaN, or infinite, a NaN, an infinite horizon, a mean motion of 0 and below, negative thresholds, unordered intervals, unordered burns, burns before 0 and after `T`, a run out of fuel in each search and at accuracy 0, and overflows of a threshold's square and of the state.  `verified-cases-passivesafety --panels` prints the panels that each case's searches evaluate, counted by the least fuel with which each search finishes, and `ellipseCap` and `hopShortCap` give their searches about 10% more fuel than the most panels of one search, which a costlier enclosure or a record for each search exceeds.

## Limits of the theorems

The theorems concern the Hill–Clohessy–Wiltshire model.  Its accuracy for a mission, the circular orbit of the chief, the neglect of perturbations, and the impulsive burns are the caller's.  The box must contain the true relative state and each burn's box its executed velocity change, and the burns must execute at the plan's times.  The theorems bound no width.  The accuracy relates each bound to the least componentwise bound at the panels' midpoints, which can lie below the true minimum, and the tests measure both gaps.  A program that ignores `acc` satisfies the theorems, and a conservative bound rejects a safe plan with status 3 or 4.  A program that rejects every plan, or that reports a wrong scenario or `stop` on a rejection, satisfies the theorems, and the cases test those fields.  The C translation has its theorem but no native driver that builds and runs it, and an image of the AArch64 back end is an open item.  The planner, the choice of the thresholds and the horizon, and any converter that produces the input lie outside the theorems, which rest on the verified compiler's trusted base, described in [the trusted-base document](../../docs/trusted-base.md).

## References

- [Passive-safety check requirements](requirements.md)
- [The interval library](../../Library/Numerics/Interval/README.md)
- W. H. Clohessy and R. S. Wiltshire, Terminal guidance system for satellite rendezvous, Journal of the Aerospace Sciences 27(9), 1960, 653–658.  https://doi.org/10.2514/8.8704
- S. D'Amico and O. Montenbruck, Proximity operations of formation-flying spacecraft using an eccentricity/inclination vector separation, Journal of Guidance, Control, and Dynamics 29(3), 2006, 554–563.  https://doi.org/10.2514/1.15114
- W. Fehse, Automated Rendezvous and Docking of Spacecraft, Cambridge University Press, 2003.  https://doi.org/10.1017/CBO9780511543388
