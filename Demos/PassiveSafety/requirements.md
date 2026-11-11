# Passive-safety check requirements

## Purpose and scope

The program decides whether a plan of impulsive burns for a deputy spacecraft near a chief in a circular orbit keeps a minimum separation from the chief, under the Hill–Clohessy–Wiltshire model, when every burn executes and when any one burn is missed.  It takes a box of initial relative states, which covers the navigation error, and a box of velocity changes for each burn, which covers the execution error.  It returns a lower bound on the separation over a horizon and a lower bound on the distance in the radial and cross-track plane for all time after each scenario's last burn, each over every scenario, and it accepts the plan only when both bounds meet their thresholds.  An unproved planner proposes the plan, and the program authorizes it or not, as the authorizer of [the energy demo](../Energy/README.md) does.  The theorems cover accepted results only.

The first iteration leaves out a chief in an eccentric orbit, which needs the Yamanaka–Ankersen solution, and perturbations such as J2 and drag.  It also leaves out relative orbital elements as input, finite burns, errors in the times of burns, keep-out regions other than a sphere about the chief, and collision probability.  An image for a processor on board is an open item.

## The model

The frame is the chief's local-vertical, local-horizontal frame: `x` points radially outward from the Earth's center through the chief, `y` along the chief's velocity, and `z` along the orbit normal.  For a chief in a circular orbit of mean motion `n`, the Hill–Clohessy–Wiltshire equations are

`ẍ = 3n²x + 2nẏ`,  `ÿ = −2nẋ`,  `z̈ = −n²z`,

and as a first-order system in the state `(x, y, z, vx, vy, vz)` they are `x' = vx`, `y' = vy`, `z' = vz`, `vx' = 3n²x + 2n vy`, `vy' = −2n vx`, and `vz' = −n²z`.  With `θ = nτ`, `s = sin θ`, and `c = cos θ`, the state at time `τ` of a deputy whose state at time 0 is `(x, y, z, vx, vy, vz)` is

| Component | Value |
|---|---|
| `x(τ)` | `(4 − 3c) x + (s/n) vx + (2/n)(1 − c) vy` |
| `y(τ)` | `6(s − θ) x + y − (2/n)(1 − c) vx + ((4s − 3θ)/n) vy` |
| `z(τ)` | `c z + (s/n) vz` |
| `vx(τ)` | `3ns x + c vx + 2s vy` |
| `vy(τ)` | `−6n(1 − c) x − 2s vx + (4c − 3) vy` |
| `vz(τ)` | `−ns z + c vz` |

`Model.flow n τ s` states this closed form, for `n ≠ 0`, as the definition of the model.  Separate theorems state that it solves the first-order system at every `τ`, that it equals `s` at `τ = 0`, and that every function that solves the system at every time with the value `s` at 0 equals it, by the uniqueness theorem for differential equations with a Lipschitz right-hand side.  The equations linearize two-body motion about a circular orbit, and no theorem concerns that approximation.

A burn changes the velocity by `(Δvx, Δvy, Δvz)` at its time and leaves the position unchanged.  `Model.path n t₀ s bs t` is the state at time `t` of a deputy that has state `s` at time `t₀` and executes the burns of the list `bs` in order.  When the first burn's time is at most `t`, the definition applies the closed form from `t₀` to that time, adds the burn's velocity change, and continues from the burn's time with the rest of the list.  Otherwise it applies the closed form from `t₀` to `t` and ignores the rest of the list, so for burns in nondecreasing order of time the state at `t` includes exactly the burns at or before `t`.  The trajectory of a plan is `t ↦ Model.path n 0 s₀ bs t`.

A plan has burns `1` to `N`, and `Model.select N j bs` is the list of the burns that execute in scenario `j`:

| Scenario | Burns that execute |
|---|---|
| `0` | All |
| `k`, for `1 ≤ k ≤ N` | All but burn `k` |
| `N + k`, for `1 ≤ k ≤ N` | Burns `1` to `k − 1`, after which the deputy drifts |

Scenarios `1` to `N` model a missed burn after which the later burns still execute.  Scenarios `N + 1` to `2N` model the free drift that passive safety concerns in Fehse's account, in which a failure at burn `k` leaves the deputy without control, and scenario `N + 1` is the initial orbit.  Scenario `2N` and scenario `N` select the same burns, and so do scenarios `1` and `2` when `N = 1`.

The separation at time `t` is `√(x² + y² + z²)` of the scenario's trajectory, and the distance in the radial and cross-track plane is `√(x² + z²)`.  The last burn time `t_L` of a scenario is the time of its last executed burn, or 0 when it executes none.  The theorems state the times after the last burn as the times `t ≥ 0` at or after every burn of `Model.select N j bs`.

## Interface

```text
check  xs : Array Float, fuel : UInt64  ->  status : UInt64, scenario : UInt64,
                                            stop : Float, sep : Float, rc : Float

xs[0]          n        mean motion of the chief, radians per unit of time, n > 0
xs[1]          T        horizon, T > 0
xs[2]          dmin     separation threshold, dmin ≥ 0
xs[3]          drc      threshold of the radial and cross-track distance, drc ≥ 0
xs[4], xs[5]   x        lower and upper ends of the initial radial position
xs[6], xs[7]   y        along-track position
xs[8], xs[9]   z        cross-track position
xs[10], xs[11] vx       radial velocity
xs[12], xs[13] vy       along-track velocity
xs[14], xs[15] vz       cross-track velocity
xs[16 + 7(k−1)]                     time of burn k, 0 ≤ t₁ ≤ t₂ ≤ … ≤ t_N ≤ T
xs[17 + 7(k−1)], xs[18 + 7(k−1)]    lower and upper ends of Δvx of burn k
xs[19 + 7(k−1)], xs[20 + 7(k−1)]    Δvy of burn k
xs[21 + 7(k−1)], xs[22 + 7(k−1)]    Δvz of burn k
fuel           panels that each search may evaluate, from 1 to 1,048,576
```

The array holds `16 + 7N` values for `N` from 0 to 16 burns.  Every quantity uses one unit of length and one unit of time, such as meters and seconds, with velocities and velocity changes in their ratio.  The initial states are those at time 0, and the burn times count from it.

| Status | Meaning | Other fields |
|---|---|---|
| 0 | Accepted: both searches of every scenario met their thresholds | `sep` and `rc` hold the bounds, `scenario` and `stop` are 0 |
| 1 | The array's size is not `16 + 7N` with `N ≤ 16`, or `fuel` lies outside its range | All 0 |
| 2 | A value is not finite, `n ≤ 0`, `T ≤ 0`, `dmin < 0`, `drc < 0`, an interval has its lower end above its upper end, or the burn times are out of order or outside `[0, T]` | All 0 |
| 3 | The separation search of a scenario reached its smallest panel without a lower bound of at least `dmin` | `scenario`, and in `stop` the time at the start of the failed panel |
| 4 | The radial and cross-track search of a scenario reached its smallest panel without a lower bound of at least `drc` | `scenario`, and in `stop` the phase at the start of the failed panel |
| 5 | The separation search of a scenario used its fuel | `scenario`, and in `stop` the time at the end of the covered part |
| 6 | The radial and cross-track search of a scenario used its fuel | `scenario`, and in `stop` the phase at the end of the covered part |
| 7 | An interval operation rejected, for example on an overflow | `scenario`, and in `stop` the start of the panel; scenario 0 and `stop` 0 when the square of `dmin` or `drc` overflows |

A status from 3 to 7 ends the program at the first search that fails, with `sep` and `rc` 0.  The searches run in the order of the method, so when both searches of a scenario would fail, the status is that of the separation search.  Statuses 3 and 4 include plans that violate a threshold and plans whose bounds are too conservative to show that they meet it.

## Method

The closed form is linear in the state, and the closed form over `a + b` is the closed form over `a` after the closed form over `b`.  For burns in nondecreasing order of time from `t₀ = 0`, the position of a scenario's trajectory at `t` is therefore

`p(t) = P(t) s₀ + Σ over executed burns k of P(max(t − t_k, 0)) Δv_k`,

where `P(τ)` is the position part of the closed form and `P(τ) Δv` is the position at `τ` of a state with zero position and velocity `Δv`.  `P(0) Δv = 0`, so a burn after `t` adds nothing, and the formula holds on the whole horizon without a split at the burns.  The program evaluates the formula in [interval arithmetic](../../Library/Numerics/Interval/README.md) with the box of `s₀`, the boxes of the `Δv_k`, and an interval of `t`, so that the result contains the position of every trajectory from the boxes at every time in that interval.  The interval expression of `P` is the `enclosure_def` of `flowPosition` in `Closed.lean`, the expression of the closed-form table read with the usual precedence and left to right.  The square of the separation is the sum of the squares of the components, each the product of the absolute value with itself, and its interval is clamped to its part at or above 0, since outward rounding moves an exact 0 one step below 0.

The separation search of a scenario covers `[0, T]` with panels.  It starts at `t = 0` with the step `h = T`.  It evaluates the panel `[t, b]`, with `b = t + h` computed in binary64 and replaced by `T` when it is not finite or exceeds `T`.  When the lower end of the square of the separation over the panel is at least `d²`, the panel is accepted, `t` becomes `b`, and `h` doubles up to `T`.  Here `d²` is the upper end of the interval of `dmin · dmin` with outward rounding, or 0 when `dmin` is 0, so that a zero threshold accepts every panel.  Otherwise `h` halves, unless `h` is already at most `T·2⁻⁴⁰`, in which case the search fails with status 3.  An interval operation that rejects fails the search with status 7.  The search tests its fuel before each panel: a panel that fails at the smallest step ends the search with status 3 even when it used the last unit, and a search whose fuel runs out with `t` below `T` and no failed panel ends with status 5.  The search keeps the least lower end of its accepted panels.

The radial and cross-track components of every closed-form trajectory depend on `τ` only through `sin nτ` and `cos nτ`, so they are periodic with period `2π/n`, whether or not the along-track motion drifts.  After the last burn time `t_L` of a scenario, every term of the formula for `p` has this property, so for every `t ≥ t_L` the radial and cross-track distance at `t` equals its value at `t_L + φ/n` for some phase `φ` in `[0, 2π)`.  The radial and cross-track search covers `[0, P]` in `φ`, where `P` is the binary64 number just above `2π`, with the same panels, steps, fuel, and statuses 4, 6, and 7.  It evaluates the formula for `p` at the interval `t_L + [a, b]/n` of a panel `[a, b]` and tests the lower end of `x² + z²` against `r²`, defined from `drc` as `d²` is from `dmin`.  The brief's closed form of the minimum for bounded motion, `vy = −2n x` after the last burn, does not apply, since a box of states does not satisfy that equation.  For a point state with bounded motion, the minimum over `φ` is the minimum radial and cross-track separation of the relative eccentricity and inclination vectors that D'Amico and Montenbruck describe, and `rc` is a lower bound of that minimum over the box.

The program checks the layout and the values, then runs, for each scenario from 0 to `2N`, the separation search and then the radial and cross-track search.  It returns status 0 when all of them succeed, with `sep` the larger of `dmin` and the lower end of the interval square root of the least lower end over all separation searches, and `rc` the same from `drc` and the radial and cross-track searches.  The library's `sin` and `cos` lie within one step of the nearest-even rounding of the real functions, and the interval operations `sinI` and `cosI` enclose the sine and cosine of every point of an interval from one value at its middle.  The radial and cross-track test applies to every scenario, including the initial orbit, so a plan whose trajectories cross the along-track axis after their last burn, such as a V-bar approach, needs `drc = 0`, which accepts every panel.

## Theorems

| Theorem | Statement |
|---|---|
| `Model.flow_hasDerivAt` | For `n ≠ 0` and every `τ`, the six components of `t ↦ Model.flow n t s` have at `τ` the derivatives of the first-order system. |
| `Model.flow_zero` | `Model.flow n 0 s = s`. |
| `Model.flow_unique` | For `n ≠ 0`, a function whose components have at every time the derivatives of the first-order system, and whose value at 0 is `s`, equals `t ↦ Model.flow n t s`. |
| `Model.flow_add` | For `n ≠ 0`, `Model.flow n (a + b) s = Model.flow n a (Model.flow n b s)`. |
| `Model.path_eq` | For burns in nondecreasing order of time, `Model.path` is the closed form from the initial state plus the closed forms of the velocity changes of the burns at or before `t`, from which the formula of the method follows. |
| `Model.flow_phase` | For `n ≠ 0`, every `τ` has a `φ` in `[0, 2π)` at which the radial and cross-track components of the closed form at `φ/n` equal those at `τ`. |
| `check_input` | When `check` returns status 0, the array holds `16 + 7N` values with `N ≤ 16`, the box of initial states and the plan's boxes are not empty, and every list of burns that matches the plan is in nondecreasing order of time in `[0, T]`. |
| `check_sound` | When `check` returns status 0, the real values of the inputs satisfy `n > 0`, `T > 0`, `dmin ≥ 0`, and `drc ≥ 0`, and `dmin ≤ sep` and `drc ≤ rc`.  For every initial state in the box, every list of `N` burns at the plan's times with velocity changes in the plan's boxes, and every scenario from 0 to `2N`, the separation at every `t` in `[0, T]` is at least `sep`, and the radial and cross-track distance at every `t ≥ 0` at or after every burn of the scenario is at least `rc`. |
| `check_passive` | When `check` returns status 0, the separation of every such trajectory at every `t ≥ 0` is at least the smaller of `dmin` and `drc`. |
| `compiled.check.implements`, `check_call` | The module's export `check` returns the words of `check xs fuel` without a trap. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  A program that rejects every plan satisfies the theorems, and so does one that reports a wrong scenario or `stop` on a rejection, so the tests require the statuses and scenarios of the cases.

## Target, memory, and cost

The target is the ground: the verified compiler's WebAssembly module, run by a host such as Wasmtime, and its translation to C where the compiler's translation accepts the module.  The program allocates nothing, so its theorem needs no premise on free memory, and it reads the tables of `sin` and `cos` from the module's data.  Each search evaluates at most `fuel` panels, and a panel of either search evaluates the closed form `N + 1` times, so a call evaluates at most `2(2N + 1)(N + 1) fuel` closed forms, each with one `sin` and one `cos`.  The Cortex-M7 back end rejects floating point, so the program has no image for it, and an image of the AArch64 back end, which runs binary64 programs, is an open item.

## Tests

The model test compares the closed form with a numerical integration of the equations, by a fixed-step fourth-order Runge–Kutta method in Python, independent of the closed form.  The soundness test runs the program on plans that it should accept, samples initial states and velocity changes from the boxes, including their corners, integrates every scenario, and requires the sampled minima of the separation over `[0, T]` and of the radial and cross-track distance over one period after the last burn time to be at least `sep` and `rc`.  It reports the gap between each bound and the sampled minimum.  For a rejection with status 3 or 4, the test integrates the named scenario from samples of the boxes and reports whether a sample violates the threshold.  The cases fix the expected status and scenario, and they include a plan whose nominal trajectory passes within `dmin`, a plan whose drift after a missed burn does, relative orbits whose radial and cross-track distance falls below `drc`, plans with burns at generic phases and nonzero components, and inputs for statuses 1, 2, 5, 6, and 7.  The module test compares the module with native Lean bit for bit on the cases.

## What lies outside the theorems

The theorems concern the Hill–Clohessy–Wiltshire model.  Its accuracy for the mission, the circular orbit of the chief, the neglect of perturbations, and the impulsive burns are the caller's.  The box must contain the true relative state and each burn's box its executed velocity change, and the burns must execute at the plan's times.  The theorems bound no width: a sound bound may lie far below the true minimum, and the program then rejects a safe plan.  The planner, the choice of the thresholds and the horizon, and any converter that produces the input lie outside the theorems.

## References

- [The energy demo](../Energy/README.md)
- [The interval library](../../Library/Numerics/Interval/README.md)
- W. H. Clohessy and R. S. Wiltshire, Terminal guidance system for satellite rendezvous, Journal of the Aerospace Sciences 27(9), 1960, 653–658.  https://doi.org/10.2514/8.8704
- S. D'Amico and O. Montenbruck, Proximity operations of formation-flying spacecraft using an eccentricity/inclination vector separation, Journal of Guidance, Control, and Dynamics 29(3), 2006, 554–563.  https://doi.org/10.2514/1.15114
- W. Fehse, Automated Rendezvous and Docking of Spacecraft, Cambridge University Press, 2003, chapter 4.  https://doi.org/10.1017/CBO9780511543388
