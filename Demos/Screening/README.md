# Conjunction screening

[The program](Program.lean) screens two space objects on Kepler orbits for close approaches during a window of time.  It applies the apogee–perigee filter and the orbit-path filter, and when neither excludes the pair, it returns intervals of time that hold every time of the window at which the two trajectories come within a threshold.  [The theorems](#theorems) state that a pair that a filter excludes never comes within the threshold at any time, that every close approach of the window lies in a returned interval, and that an interval marked certain holds a close approach.  A padding input extends the guarantee to any trajectories that stay within the padding of the Kepler trajectories, which is how perturbations enter.  [The requirements](requirements.md) define the model and the interface, and [the review](review.md) records the decisions, the independent review, and the response to each finding.

`verified_compile` compiles the program, with the interval operations, the library's `sin` and `cos`, and an enclosure of the root of Kepler's equation, into a module of 47,808 bytes.  This is the first iteration of candidate 5 of the space-operations plan.  It covers one pair in the two-body model, and the SGP4 model follows, since [`Demos.Sgp4.sgp4Box_sound`](../Sgp4/BoxSound.lean) already encloses the SGP4 position over an interval of time.

## Example

Two circular orbits of 7,000 and 7,001 km, one equatorial and one polar, have both their epochs at minute 100 with a mean anomaly of zero, so both objects pass the ascending node on the x-axis at minute 100, 1 km apart.  Their periods differ by 0.02 percent, so they meet at a node every half period while their phases drift apart.  With `μ = 398600.4418` km³/s², the window `[0, 1440]` minutes, `D = 5` km, `P = 0`, both filters on, `Lp = 20`, `Cp = 4096`, `L = 20`, and `C = 65536`, the module returns status 0, path verdict 2, 1,561 cell tests, and three intervals, each marked certain:

| `lo` (min) | `hi` (min) |
|---|---|
| 51.417388916015625 | 51.431121826171875 |
| 99.99069213867188 | 100.008544921875 |
| 148.56948852539062 | 148.58322143554688 |

The apogee–perigee filter keeps the pair, since both radii are about 7,000 km, and the orbit-path filter finds the two paths within 5 km of each other at the nodes.  The oracle's minima at these meetings are 3.48, 1.00, and 3.48 km, and at the meetings near minutes 2.85 and 197.15 they are 6.74 km, so `screen_cover` states that no other time of the day has a separation of at most 5 km.

## The model

An object has the semimajor axis `a` in km, the eccentricity `e`, the inclination `i`, the right ascension of the ascending node `Ω`, the argument of perigee `ω`, and the mean anomaly `M₀` in degrees at its epoch `τ` in minutes.  With the gravitational parameter `μ`, the mean motion is `n = 60 √(μ/a³)` radians per minute, the eccentric anomaly `E(t)` is the root of `E − e sin E = M₀ π/180 + n (t − τ)`, and the position is `r(t) = a (cos E − e) p̂ + a √(1 − e²) sin E q̂`, with the unit vectors `p̂` toward the perigee and `q̂` a quarter turn ahead of it.  [The model](Model.lean) defines these as real functions, and [the specification](Spec.lean) states each part of the program's computation once with [`enclosure_def`](../../Library/Numerics/Interval/README.md#one-source-for-a-real-function-and-its-interval-program), which declares the real function, its interval program, and the theorem that the interval program encloses it.  The separation `s(t)` is the distance between the two positions, and a close approach is a time `t` of the closed window `[t₀, t₁]` with `s(t) ≤ D`.

The threshold of every test is `T = D + P`, with the padding `P`.  For trajectories `ρ₁` and `ρ₂` within `δ₁` and `δ₂` of the Kepler trajectories, with `δ₁ + δ₂ ≤ P`, a separation of at most `D` puts the Kepler trajectories within `T`.  The padding is the caller's premise, since no theorem bounds the distance of an SGP4 trajectory or a true orbit from its Kepler trajectory.

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding, and a test whose intervals are rejected excludes nothing.

| Part | Test | Proof |
|---|---|---|
| Apogee–perigee filter | One object's perigee radius `a (1 − e)` exceeds the other's apogee radius `a (1 + e)` by more than `T` | Every point of a path lies between the two radii (M1), and the triangle inequality |
| Orbit-path filter | Branch-and-bound over two eccentric anomalies from `[0, 6.5]²`: a cell is dropped when the boxes of the two paths over it lie farther apart than `T`, and the search stops with verdict 2 when the path points at a cell's center lie within `T` | Every position is a path point at an anomaly in `[0, 2π]` (M2), and the cells that remain cover every pair of anomalies whose points lie within `T` |
| Isolation | Bisection of `[t₀, t₁]` over `L` levels: a cell is dropped when `s(m)` exceeds `T + (V₁ + V₂) ρ`, with `m` the cell's computed middle, `ρ` the distance from `m` to the cell's ends, and `Vₖ = aₖ nₖ / (1 − eₖ)` | Each object moves at most `Vₖ` km per minute (M3) |

The isolation keeps a cell unsplit when its middle does not lie strictly inside it or when every time of it lies within `T` by the speed bound.  At more than `C` cells it keeps the previous level and reports status 3.  A final pass marks a cell certain when its computed middle lies in it and within `T`, and consecutive kept cells that touch merge.  M3 rests on two facts: Kepler's equation rises with slope at least `1 − e`, which `Demos.Sgp4.Kepler.growth` states, so the eccentric anomaly moves at most `n/(1 − e)` per minute, and a point of the path moves at most `a` per unit of eccentric anomaly, since a chord of the unit circle is no longer than its arc.

## Interface

```text
input   index    value                                   requirement
        0        version                                 1
        1..7     object 1: a, e, i, Ω, ω, M₀, τ          a > 0, 0 ≤ e < 1
        8..14    object 2, in the same order             a > 0, 0 ≤ e < 1
        15       μ (km³/s²)                              μ > 0
        16, 17   t₀, t₁ (min)                            -1e9 ≤ t₀ ≤ t₁ ≤ 1e9
        18, 19   D, P (km)                               D ≥ 0, P ≥ 0
        20       apogee–perigee filter                   0 skip, 1 apply
        21, 22   orbit-path levels Lp and cap Cp         whole, 0 ≤ Lp ≤ 40, 1 ≤ Cp ≤ 2^20
        23, 24   isolation levels L and cap C            whole, 0 ≤ L ≤ 60, 1 ≤ C ≤ 2^20
        Every value is finite, and the array holds exactly 25 values.

output  0        status
        1        K, the number of intervals
        2        path verdict
        3        cell tests of both searches
        4        isolation levels completed
        5 + 3j   interval j: lo, hi (min), and 1 when it holds a time within T

status   0  isolation complete            path verdict  0  not run
         1  excluded by apogee–perigee                  1  excluded
         2  excluded by orbit path                      2  paths within T
         3  isolation stopped at C                      3  undecided after Lp levels
         4  invalid input: 4, 0, 0, 0, 0                4  stopped at Cp
```

## Parts

| Part | File | Content |
|---|---|---|
| Model | [`Model.lean`](Model.lean) | Orbits, positions, paths, the distance, and M1 to M3 |
| Enclosures | [`Spec.lean`](Spec.lean), [`KeplerBox.lean`](KeplerBox.lean) | The interval programs of the orbit's quantities, a path point, the eccentric anomaly, and the squared distance, with their enclosure theorems |
| Program | [`Program.lean`](Program.lean), [`Flat.lean`](Flat.lean) | The filters, the isolation, the merge, the input check, and `screen` |
| Searches | [`Cover.lean`](Cover.lean) | `loop_cover` and `loop_size_le` for loops that refine an array of cells |
| Proofs | [`Filters.lean`](Filters.lean), [`Isolation.lean`](Isolation.lean), [`Soundness.lean`](Soundness.lean) | F1, F2, I1, I2, and S1 |
| Module | [`Verified.lean`](Verified.lean), [`Call.lean`](Call.lean), [`File.lean`](File.lean) | The compilation, C1, and the file theorems |

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/screening/Axioms.lean) reports.  The real value of a float is the real number that it represents, and for an input `xs`, `orbitIn xs 1` and `orbitIn xs 8` are the orbits of the real values of the elements, `separation xs t` is the distance of their positions at `t`, `threshold xs` is `D + P`, and `Returned out t` states that `t` lies between the ends of interval `j` of the output for some `j` with `7 + 3j` below the output's size.  `valid xs` is the input check of the interface.

| Code | Theorem | File | Statement |
|---|---|---|---|
| M1 | `frame`, `path_radius` | [Model](Model.lean) | `p̂` and `q̂` are orthonormal, and for `a > 0` and `0 ≤ e < 1` every point of a path lies between `a (1 − e)` and `a (1 + e)` from the origin. |
| M2 | `position_path`, `path_reduce` | [Model](Model.lean) | The position at `t` is the path point at the eccentric anomaly at `t`, and every path point is the point at an anomaly in `[0, 2π]`. |
| M3 | `position_lipschitz` | [Model](Model.lean) | `\|r(t) − r(t')\| ≤ (a n / (1 − e)) \|t − t'\|`. |
| | `kepler.encloses`, `Spec.orbit.encloses`, `Spec.pathPoint.encloses`, `Spec.anomaly.encloses`, `Spec.distSq.encloses` | [Enclosures](KeplerBox.lean), [specification](Spec.lean) | Each interval program encloses its real function when its arguments enclose theirs. |
| F1 | `apsidesExclude_sound`, `screen_apsides` | [Filters](Filters.lean), [soundness](Soundness.lean) | When the apogee–perigee filter excludes the pair, every point of one path lies farther than `D + P` from every point of the other, and for a valid input with status 1, `threshold xs < separation xs t` for every real `t`. |
| F2 | `pathFilter_sound`, `screen_path`, `screen_path_close` | [Filters](Filters.lean), [soundness](Soundness.lean) | Path verdict 1 puts every point of one path farther than `D + P` from every point of the other, so status 2 gives `threshold xs < separation xs t` for every real `t`.  Path verdict 2 gives two path points within `D + P`. |
| I1 | `spanTest_zero`, `isolate_inv`, `screen_cover` | [Isolation](Isolation.lean), [soundness](Soundness.lean) | A cell that the test excludes holds no time within `D + P`, and for a valid input, every `t` of the window with `separation xs t ≤ threshold xs` satisfies `Returned (screen xs) t`. |
| I2 | `spanTest_certain`, `screen_certain` | [Isolation](Isolation.lean), [soundness](Soundness.lean) | For a valid input, an interval whose certainty is 1 holds a `t` with `separation xs t ≤ threshold xs`. |
| I3 | `spanStep_inside`, `screen_within` | [Isolation](Isolation.lean), [soundness](Soundness.lean) | For a valid input, every returned interval lies in `[t₀, t₁]`. |
| S1 | `screen_sound`, `screen_excluded` | [Soundness](Soundness.lean) | For a valid input and trajectories `ρ₁` and `ρ₂` within `δ₁` and `δ₂` of the Kepler trajectories on the window, with `δ₁ + δ₂ ≤ P`, every `t` of the window with `\|ρ₁(t) − ρ₂(t)\| ≤ D` satisfies `Returned (screen xs) t`, and for an output of five values, `D < \|ρ₁(t) − ρ₂(t)\|` at every `t` of the window. |
| | `screen_invalid` | [Soundness](Soundness.lean) | Status 4 holds exactly when `valid xs` is false. |
| C1 | `screen_callSpec`, `screen_callBits`, `screen_call` | [Call](Call.lean) | Function 84, the export `screen`, called from a ready store with the bit patterns of `xs` borrowed and room for `top` to rise by `compiled.screen.bound xs` bytes, returns without a trap a new array that holds the bit patterns of `screen xs`, and leaves a ready store.  The module's bytes decode to the module, and its start store is ready. |
| | `compiled.bytes`, `screening_file`, `screening_file_decode` | [Compilation](Verified.lean), [file theorems](File.lean) | `encode compiled.module` succeeds with bytes that decode to the module, and `build/verified/screening.wasm` holds them. |

The searches share one loop lemma, `loop_cover` of [`Cover.lean`](Cover.lean): a loop that appends to an array the children of each cell of another, keeping the array built so far as a prefix, leaves every point that a cell holds and that no step excludes in a child.  The orbit-path filter's invariant `PathInv` and the isolation's `IsoInv` carry that covering from level to level, with at most `2²⁰` cells so that the conversions of the sizes to words are exact.

## Tests

`tests/verified/run.sh --cases screening` writes the module, validates it, compares `screen` with native Lean on [the module cases](../../tests/TestSupport/Screening/Cases.lean), runs the axiom audit, and checks the file theorems.  The cases hold two crossing circular orbits, pairs that each filter excludes, a pair at the cap, an eccentric orbit, invalid inputs, and 12 pairs of low orbits from a linear congruential generator.  All 23 cases agree with native Lean bit for bit, and the 27 theorems of the audit report only the three permitted axioms.

[The oracle](../../tests/screening/oracle.py) checks the module against dense sampling of the two-body model, written apart from the program.  It propagates both orbits with its own solver of Kepler's equation, in binary64 at a step of `5 · 10⁻⁴` minutes with both ends of the window sampled and in mpmath at 30 digits to refine each sampled minimum, and it finds the least distance between the two paths from a grid of eccentric anomalies refined by golden-section search.  [The requirements](requirements.md#tests) list its checks: every sampled time and refined minimum below `T` in a returned interval, every certain interval with a time within `T`, every exclusion with a separation and a path distance above `T`, and outcomes that the method must reach where the margins exceed rounding by far.  [The harness](../../tests/screening/screen.mjs) calls the module under Node in a fresh instance for each case.

```sh
uv run tests/screening/oracle.py build/verified/screening.wasm --mutate
```

All 64 cases pass, 53 valid inputs and 11 invalid ones, and no sample or minimum falls within `10⁻⁶` km of `T`.  In each of the 25 cases with a sampled separation below `T`, the mutation run makes two altered outputs, one without the interval that holds the deepest minimum and one with status 1, and it returns the whole window in 32 cases.  The checks reject all 82 altered outputs.  [The review](review.md#wrong-programs) ran the reviewer's 24 wrong programs through the same checks, and they rejected all but one, a path search from `[0, fl(2π)]²` that only the proof excludes.

## Cost of a pair

`uv run tests/screening/oracle.py build/verified/screening.wasm --cost` times each call as the median of nine calls in Node 24.13 on a four-core AArch64 virtual machine, while other jobs used three of the cores.  The time includes the setup of both objects in every call.

| Pairs | Cases | Cell tests, mean | Cell tests, most | ms, mean | ms, most |
|---|---|---|---|---|---|
| Excluded by the apogee–perigee filter | 2 | 0 | 0 | 0.01 | 0.01 |
| Low orbits drawn at random, most excluded by a filter | 10 | 334 | 906 | 0.69 | 1.91 |
| Crossing paths, path verdicts 1, 3, and 4 | 4 | 776 | 2,183 | 2.70 | 8.52 |
| One day with one constructed approach | 10 | 1,130 | 1,613 | 3.25 | 7.10 |
| Ten hours of orbits that meet every half orbit, cut off at a meeting | 4 | 1,848 | 2,800 | 5.18 | 7.77 |
| Eccentric orbits | 4 | 1,425 | 2,717 | 4.27 | 8.30 |
| Nearly coplanar orbits | 3 | 9,969 | 16,384 | 35.8 | 57.9 |
| One week with orbits that meet every half orbit | 3 | 13,687 | 17,625 | 49.3 | 65.7 |
| Padding cases, among them circles 2 km apart that stay within `T` | 7 | 11,191 | 69,496 | 39.5 | 247.7 |
| Enclosures that reject, every cell kept | 1 | 213,417 | 213,417 | 515 | 515 |

A pair that a filter excludes costs at most a few milliseconds, and a pair kept for the isolation of a day with one constructed approach costs up to 1,613 cell tests of both searches and up to 7.1 ms.  The cost grows with the time that the separation stays near `T`, so nearly coplanar orbits and concentric circles cost the most.  The orbits of each week case share a period, so they meet every half orbit, and each week case returns more than 200 intervals.

## Limits

The theorems concern Kepler trajectories, and trajectories within the padding of them by the caller's premise.  No theorem bounds the distance of an SGP4 trajectory or of a true orbit from its Kepler trajectory, and that distance grows with the time from the epoch: Woodburn, Coppola, and Stoner trace the classical filters' misses to perturbations, which put an apogee from osculating elements about 20 km in error and move the distance between two paths from 0 to about 90 km over a day.  The choice of `D`, `P`, and the frame, and the relation of the elements to the objects, are the caller's.

The theorems bound no width and no count.  A coarse result is sound, and the number and lengths of the intervals depend on `L`, `C`, and the rounding.  The tests check the bound `T + (V₁ + V₂) w` on every returned time, and no theorem states it.  Path verdicts 3 and 4 and status 3 carry no statement beyond I1.  No theorem states that a certain interval holds a local minimum of the separation.  C1 states the generated allocation bound `compiled.screen.bound`, for which no closed form is proved, and no test covers the C translation or an AArch64 image.  The catalog version and the SGP4 model are later iterations.

## References

- [Conjunction screening requirements](requirements.md)
- [Conjunction screening: decisions and review](review.md)
- [J. Woodburn, V. Coppola, and F. Stoner, A description of filters for minimizing the time required for orbital conjunction computations, AAS 09-372, 2009](https://www.agi.com/getmedia/d56ede5a-efe7-48de-af8b-c122117496af/A-Description-of-Filters-for-Minimizing-the-Time-Required-for-Orbital-Conjunction-Computations.pdf?ext=.pdf)
- [S. Alfano, Toroidal path filter for orbital conjunction screening, Celestial Mechanics and Dynamical Astronomy 113, 2012, 321–334](https://link.springer.com/doi/10.1007/s10569-012-9421-3)
