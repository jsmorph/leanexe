# Event windows

[The program](Program.lean) finds the times of a window at which a spacecraft on a Kepler orbit is in the Earth's shadow, or at which a vector fixed in the inertial frame or in the orbit's radial, along-track, and cross-track frame lies within an exclusion angle of the Sun.  It returns intervals of time, called runs, that hold every time of the window at which the event's condition holds, and it labels a run 1 when the condition holds at every time of it.  [The theorems](#theorems) state that no time of the condition lies outside the runs, that the condition holds throughout every run labeled 1, and that every crossing of the condition lies in a run and at an end of every run labeled 1 that holds it.  A padding input extends the first two statements of the shadow to every trajectory within the padding of the Kepler trajectory.  [The requirements](requirements.md) define the model and the interface, and [the review](review.md) records the decisions, the independent review, and the response to each finding.

`verified_compile` compiles the program, with the interval operations, the library's `sin` and `cos`, the enclosure of Kepler's equation, and the screening demo's positions, into a module of 36,497 bytes.  This is the first iteration of candidate 5.1 of the space-operations plan.  It covers the events that need no rotation of the Earth, and the events of ground stations and targets wait on the frames candidate (5.2).

## Example

An orbit with `a = 6878` km and `e = 0.001` in the equatorial plane at the March equinox of 2026, with minute 0 at 2026-03-20 00:00 UT (`d₀ = 9574.5`), passes through the Earth's shadow once an orbit.  With the penumbral cone `α = 0.269°`, `R = 6378.137` km, `P = 0`, the window `[0, 1440]` minutes, `N = 20`, and `C = 65536`, the module returns status 0, 45 runs, and 5,111 cell tests.  The first eclipse takes three runs:

| Start (min) | End (min) | Label |
|---|---|---|
| 29.200286865234375 | 29.20440673828125 | 0 |
| 29.20440673828125 | 65.13107299804688 | 1 |
| 65.13107299804688 | 65.13381958007812 | 0 |

The oracle refines the entry to 29.2027293 minutes and the exit to 65.1325908 minutes, inside the two runs labeled 0, so each crossing is bracketed to 0.25 s and 0.16 s, and the spacecraft is in the penumbra or the umbra throughout the 35.9 minutes between them.  With the umbral cone `α = −0.264°` the oracle's crossings of the same eclipse fall at 29.3432603 and 64.9920575 minutes, 8.4 s inside each of the penumbra's.

## The model

The orbit is [the screening demo's Kepler orbit](../Screening/README.md#the-model), with the elements `a`, `e`, `i`, `Ω`, `ω`, `M₀`, and the epoch `τ`, and the gravitational parameter `μ`.  The Sun's direction is the U.S. Naval Observatory's approximate solar coordinates: for `D` days from J2000.0, `g = 357.529 + 0.98560028 D`, `λ = 280.459 + 0.98564736 D + 1.915 sin g + 0.020 sin 2g`, and `ε = 23.439 − 0.00000036 D` in degrees, and `ŝ = (cos λ, cos ε sin λ, sin ε sin λ)`.  Minute 0 of the window falls `d₀` days from J2000.0, so `D(t) = d₀ + t/1440`.  [The model](Model.lean) defines these functions over the reals, and [the specification](Spec.lean) states each interval program once with `enclosure_def`.

| Event | Condition at `t` |
|---|---|
| 1, shadow | `x ≥ 0` and `y cos α − x sin α ≤ R`, with `x = −r · ŝ` and `y = \|r × ŝ\|` |
| 2, inertial vector | The angle between `b` and `ŝ` is at most `β`: `\|b\| \|ŝ\| cos β ≤ b · ŝ` |
| 3, vector in the orbit's frame | The same for `v = b₁ R̂ + b₂ Ŝ + b₃ Ŵ`, with `R̂ = r/\|r\|`, `Ŵ = p̂ × q̂`, and `Ŝ = Ŵ × R̂` |

A positive half-angle `α` gives the penumbral cone, a negative one the umbral cone, and 0 the cylinder.  Each condition is `g₁ ≤ 0` and `g₂ ≤ 0` for two real functions with rate bounds `L₁` and `L₂`: `r · ŝ` and `y cos α + (r · ŝ) sin α − R` for the shadow, and `|b| cos β − v · ŝ` twice for the vectors.  `V = a n / (1 − e)` bounds the speed, `a (1 + e)` the radius, and `ω = ω_d / 1440` the rate of `ŝ` in radians per minute, with `ω_d = π/180 · (0.98564736 + 1.955 · 0.98560028 · π/180 + 0.00000036)` per day.  The rate bounds are `V + a (1 + e) ω` and `(|cos α| + |sin α|)` times it for the shadow, `|b| ω` for the inertial vector, and `(|b₁| + |b₂|) V / (a (1 − e)) + |b| ω` for the vector in the orbit's frame.

The padding `P` enters the shadow as margins `W₁ = P` and `W₂ = (|cos α| + |sin α|) P`.  A trajectory `ρ` within `δ ≤ P` of the Kepler trajectory has shadow functions within these margins of the Kepler trajectory's, so the cell test, which subtracts the margins for an exclusion and adds them for a whole cell, serves every such trajectory.  The padding is the caller's premise, and [the requirements](requirements.md#the-suns-direction) show how it also carries an error of the Sun's direction into the shadow's theorems.

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding, and a test whose intervals are rejected excludes nothing and marks nothing.  A cell of time `[c₀, c₁]` is tested at its computed middle `m`, with an upper bound `η` of the distance from `m` to its ends.  The test excludes the cell when the lower bound of some `gₖ(m)` exceeds the upper bound of `Lₖ η + Wₖ`, and it marks the cell whole when the upper bound of both `gₖ(m) + Lₖ η + Wₖ` is at most 0.  Each of `N` levels drops the excluded cells and splits the others at `m`, except the whole ones and those whose middle does not lie strictly inside them.  A level that would leave more than `C` cells stops the search with status 1 and the cells of the previous level.  A final pass labels each kept cell 1 when it is whole and 0 otherwise, and a cell joins the run before it when the labels agree and its start lies between the run's ends.

## Interface

```text
input   index    value                                   requirement
        0        version                                 1
        1..7     a, e, i, Ω, ω, M₀, τ                    a > 0, 0 ≤ e < 1
        8        μ (km³/s²)                              μ > 0
        9        d₀ (days from J2000.0 at minute 0)      |d₀| ≤ 1e6
        10, 11   t₀, t₁ (min)                            -1e9 ≤ t₀ ≤ t₁ ≤ 1e9
        12       event                                   1 shadow, 2 inertial vector,
                                                         3 vector in the orbit's frame
        13       α or β (degrees)                        -90 < α < 90, 0 ≤ β ≤ 180
        14       R (km), shadow                          R > 0
        15       P (km), shadow                          P ≥ 0
        16..18   b, vectors                              not all zero
        19, 20   levels N and cap C                      whole, 0 ≤ N ≤ 60, 1 ≤ C ≤ 2^20
        Every value is finite, and the array holds exactly 21 values.

output  0        status: 0 complete, 1 stopped at C, 2 invalid input (2, 0, 0, 0)
        1        K, the number of runs
        2        cell tests
        3        levels completed
        4 + 3j   run j: start, end (min), and 1 when the condition holds throughout
```

## Parts

| Part | File | Content |
|---|---|---|
| Model | [`Model.lean`](Model.lean) | Vectors, the Sun's direction, the shadow, the orbit's frame, and M1 to M3 |
| Enclosures | [`Spec.lean`](Spec.lean) | The interval programs of the Sun's direction, the event functions, the frame, and the rate bounds, with their enclosure theorems and their equations with the model |
| Program | [`Program.lean`](Program.lean), [`Flat.lean`](Flat.lean) | The cell test, the isolation, the final pass, the join, the input check, and `events` |
| Proofs | [`Isolation.lean`](Isolation.lean), [`Soundness.lean`](Soundness.lean) | The isolation for any functions within the margins, the three events, and E1 to E6 |
| Module | [`Verified.lean`](Verified.lean), [`Call.lean`](Call.lean), [`File.lean`](File.lean) | The compilation, C1, and the file theorems |

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/events/Axioms.lean) reports.  For an input `xs`, `Condition xs t` is the condition of its event for its Kepler trajectory at `t` minutes, `Returned out t` states that `t` lies between the ends of run `j` of the output for some `j` with `6 + 3j` below the output's size, and `valid xs` is the input check of the interface.

| Code | Theorem | File | Statement |
|---|---|---|---|
| M1 | `sun_unit`, `sun_lipschitz` | [Model](Model.lean) | `\|ŝ(D)\| = 1` and `\|ŝ(D) − ŝ(D′)\| ≤ ω_d \|D − D′\|`. |
| M2 | `axis_sq`, `rsw_norm` | [Model](Model.lean) | For a unit `ŝ`, `x² + y² = \|r\|²`, and for a valid orbit `\|v(t)\| = \|b\|`. |
| M3 | `shadow1_lipschitz`, `shadow2_lipschitz`, `inertial_lipschitz`, `rsw_lipschitz`, `shadow_near` | [Model](Model.lean) | Each event function changes at most at its rate bound, and a position within `δ` changes the shadow's functions by at most `δ` and `(\|cos α\| + \|sin α\|) δ`. |
| | `Spec.sunDir.encloses`, `Spec.shadowParts.encloses`, `Spec.vectorPart.encloses`, `Spec.rswVec.encloses`, `Spec.rates.encloses` | [Specification](Spec.lean) | Each interval program encloses its real function when its arguments enclose theirs. |
| | `cellTest_zero`, `cellTest_whole`, `isolate_inv`, `joinRuns_spec`, `output_spec` | [Isolation](Isolation.lean) | For any functions `h₁` and `h₂` within the margins of the event's functions on the window, an excluded cell holds no time at which `h₁ ≤ 0` and `h₂ ≤ 0`, both hold throughout a whole cell, and the runs carry both facts. |
| E1 | `events_cover` | [Soundness](Soundness.lean) | For a valid input, every `t` of the window with `Condition xs t` satisfies `Returned (events xs) t`. |
| E2 | `events_holds` | [Soundness](Soundness.lean) | For a valid input, `Condition xs t` holds at every `t` of a run labeled 1. |
| E3 | `events_within` | [Soundness](Soundness.lean) | For a valid input, every run lies in `[t₀, t₁]`. |
| E4 | `events_near` | [Soundness](Soundness.lean) | For a valid input of the shadow and a trajectory `ρ` with `dist3 (ρ t) (r t) ≤ δ ≤ P` on the window, every time of the window at which `ρ` is in the shadow lies in a run, and `ρ` is in the shadow throughout every run labeled 1. |
| E5 | `events_crossing` | [Soundness](Soundness.lean) | For a valid input, every crossing of `Condition xs` in the window lies in a run, and a crossing in a run labeled 1 is one of its ends. |
| E6 | `events_status`, `events_progress`, `isolate_status` | [Soundness](Soundness.lean), [Isolation](Isolation.lean) | For a valid input, the status is 0 or 1, outputs 0 and 3 are the search's status and levels, status 0 comes with all `N` levels, and status 1 with fewer levels and a next level of more than `C` cells. |
| | `events_invalid` | [Soundness](Soundness.lean) | Status 2 holds exactly when `valid xs` is false. |
| C1 | `events_callSpec`, `events_callBits`, `events_call` | [Call](Call.lean) | Function 85, the export `events`, called from a ready store with the bit patterns of `xs` borrowed and room for `top` to rise by `compiled.events.bound xs` bytes, returns without a trap a new array that holds the bit patterns of `events xs`, and leaves a ready store.  The module's bytes decode to the module, and its start store is ready. |
| | `compiled.bytes`, `events_file`, `events_file_decode` | [Compilation](Verified.lean), [file theorems](File.lean) | `encode compiled.module` succeeds with bytes that decode to the module, and `build/verified/events.wasm` holds them. |

The proofs of [`Isolation.lean`](Isolation.lean) hold for any event with two functions, rate bounds, and margins that its intervals enclose (`Sound`), so the three events and the padding share one proof.  The searches reuse the screening demo's loop lemmas `loop_cover` and `loop_size_le`, and the invariant `IsoInv` carries the covering from level to level with at most `2²⁰` cells.

## Tests

`tests/verified/run.sh --cases events` writes the module, validates it, compares `events` with native Lean on [the module cases](../../tests/TestSupport/Events/Cases.lean), runs the axiom audit, and checks the file theorems.  The cases hold the three cones and a padding on a low orbit, a geostationary and a Molniya orbit, the two vector events, the caps, rejected enclosures, invalid inputs, and 12 inputs from a linear congruential generator.  All 28 cases agree with native Lean bit for bit, and the 34 theorems of the audit report only the three permitted axioms.

[The oracle](../../tests/events/oracle.py) checks the module against dense sampling of the model, written apart from the program.  It solves Kepler's equation and evaluates the USNO formula and each event's functions on its own, in binary64 at a step of `10⁻³` minutes with both ends of the window sampled, and in mpmath at 30 digits for samples near zero and for the refinement of each crossing to `10⁻¹⁰` minutes.  [The requirements](requirements.md#tests) list its checks: the stated status and counts, the order of the runs, every sampled and refined time of the condition in a run, every sampled and refined time without it outside the runs labeled 1, the same for trajectories displaced by the padding, and the method's bound on the runs where the margins far exceed rounding.  [The harness](../../tests/events/events.mjs) calls the module under Node in a fresh instance for each case.

```sh
uv run tests/events/oracle.py build/verified/events.wasm --mutate
```

All 64 cases pass, 45 valid inputs and 19 invalid ones, with 1,096 refined crossings, those of the displaced trajectories among them, and no sample is inconclusive.  The mutation run makes 233 altered outputs, each wrong by construction, and the checks reject all of them.  The review's model ran its 35 wrong programs through the same kinds of checks, and [the review](review.md#wrong-programs) lists the cases that reject each and the four that no case can reject.

## Cost

`uv run tests/events/oracle.py build/verified/events.wasm --cost` times each call as the median of nine calls in Node 24.13 on a four-core AArch64 virtual machine.  A cell test takes about 4 µs.

| Cases | Cell tests | ms |
|---|---|---|
| A day of a low orbit's eclipses, any cone | 5,085 to 5,127 | 19.9 to 20.8 |
| The same with a padding of 5 km and of 50 km | 7,657 and 25,929 | 29.9 and 101.0 |
| Grazing passes, `β` from 67.5° to 68.1° | 23,931 to 29,003 | 92.1 to 111.5 |
| A day at the geostationary radius | 19 to 222 | 0.09 to 0.89 |
| An along-track vector at 30°, a day | 4,074 | 20.0 |
| An inertial vector over a week at `N = 24` | 11,946 | 25.9 |

The cost grows with the time that a function stays near zero, so grazing passes and wide margins cost the most.

## Limits

The theorems concern the model: Kepler motion, the USNO's formula, a spherical Earth with a shadow cone of fixed half-angle, and an attitude fixed in the inertial frame or in the orbit's frame.  The formula's accuracy of about 1′, the frame of the elements, the parallax of the Sun for the exclusion events, the cone's half-angle, `R`, and `P` are the caller's premises, and [the requirements](requirements.md#the-suns-direction) give the margins that carry them into the theorems.  No theorem bounds the distance of an SGP4 trajectory or a true orbit from its Kepler trajectory.

The theorems bound no width and no count.  An output that labels every run 0, or returns the whole window as one run, satisfies E1 to E6, and the program's text, which C1 ties to the module, and the oracle's method checks exclude it.  No theorem states that the runs are in order or that runs with equal labels do not touch, which the oracle checks.  E5 concerns the Kepler trajectory.  C1 states the generated allocation bound `compiled.events.bound`, for which no closed form is proved, and no test covers the C translation or an AArch64 image.  The events of ground stations and targets wait on the frames candidate, and the output does not feed the slew planner.

## References

- [Event windows requirements](requirements.md)
- [Event windows: decisions and review](review.md)
- [U.S. Naval Observatory, Approximate solar coordinates](https://aa.usno.navy.mil/faq/sun_approx)
- [The conjunction screening demo](../Screening/README.md)
