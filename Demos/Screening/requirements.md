# Conjunction screening requirements

## Purpose and scope

The program screens two space objects for close approaches during a window of time.  It applies two filters that may exclude the pair, and when they do not, it returns intervals of time that contain every time of the window at which the two trajectories come within a threshold.  Each filter and the isolation carry a theorem: a pair that a filter excludes never comes within the threshold, and every close approach lies in a returned interval.  The classical filters of Hoots, Crawford, and Roehrich (1984) can exclude pairs that do come close, as Woodburn, Coppola, and Stoner (2009) and Alfano (2012) report, and these requirements replace each filter's test with one that a proof covers.

This iteration covers one pair.  A catalog version would run the filters over every pair of a catalog, and it waits on the cost per pair that the tests measure.

## Prerequisite: SGP4 boxes over an interval of time

`Demos.Sgp4.sgp4Box_sound` takes the time as an interval `t` and concludes, for every real `t'` that `t` encloses, that a result with status 0 or 6 contains the model's position and velocity at `t'`.  One evaluation over `[t₀, t₀ + h]` therefore encloses the SGP4 position at every time of that interval, and no extension of `BoxSound.lean` is needed.  A run of `sgp4Box` over intervals of width `h` from `10⁻⁴` to 1,440 minutes, for the element sets 06251, 28057, and 00005 of the Vallado verification file, measured each coordinate's width against the range of 401 samples of the binary64 program.  Up to `h = 1` minute the width of each coordinate is about the speed times `h`, 470 km per minute for 06251, so the box is about 1.5 times the sampled range of the coordinate that moves fastest and wider for the others.  The sine and cosine enclosures are clamped to `[-1, 1]`, so the widths stop growing near the extent of the orbit, and for the eccentric orbit 00005 a box over the 1,440 minutes after the 360th returns status 7.  An interpreted evaluation of one box took about 3.9 ms.

## Trajectory model

The first model is two-body motion.  The second model, SGP4, follows in a later iteration with the interval boxes above.  Two-body motion comes first for three reasons.  The classical filters are statements about Kepler orbits, so a filter proved sound for them answers the reports of missed conjunctions on their own terms.  The isolation's exclusion of a time interval needs a bound on the relative speed that holds for the model, and Kepler's equation gives one by algebra, while SGP4's velocity output is not the derivative of its position, so a bound for SGP4 would need the derivative of the whole SGP4 computation.  The orbit-path filter needs a fixed path for each object, which an SGP4 trajectory does not have.

An object has the semimajor axis `a` in km, the eccentricity `e`, the inclination `i`, the right ascension of the ascending node `Ω`, the argument of perigee `ω`, and the mean anomaly `M₀` in degrees at its epoch `τ`, in minutes on the window's time scale.  Both objects use one gravitational parameter `μ` in km³/s² and one inertial frame.  The mean motion is `n = 60 √(μ / a³)` in radians per minute, and at time `t` in minutes the mean anomaly is `M(t) = M₀ π/180 + n (t − τ)`.  The eccentric anomaly `E(t)` is the root of `E − e sin E = M(t)`, which is unique for `0 ≤ e < 1` (`Demos.Sgp4.Kepler.exists_unique_root` with `a = e` and `b = 0`).  The position in km is

`r(t) = a (cos E − e) P + a √(1 − e²) sin E Q`,

with the unit vectors toward the perigee and a quarter turn ahead of it, for the angles in radians,

`P = (cos ω cos Ω − sin ω sin Ω cos i, cos ω sin Ω + sin ω cos Ω cos i, sin ω sin i)`,
`Q = (−sin ω cos Ω − cos ω sin Ω cos i, −sin ω sin Ω + cos ω cos Ω cos i, cos ω sin i)`.

These are the formulas of `Demos.Sgp4.twoBody` with `a` in km in place of Earth radii.  The separation is `s(t) = |r₁(t) − r₂(t)|`, the Euclidean distance in km.  The path of an object is the set `{p(E) : E real}`, where `p(E)` is the position above for the eccentric anomaly `E`, an ellipse with a focus at the origin.

## Close approaches, the window, and perturbations

A close approach is a time `t` of the window `[t₀, t₁]` with `s(t) ≤ D`, for a threshold `D ≥ 0` in km.  Every local minimum of the separation in the window whose value is at most `D` is such a time, and so is each end of the window at which the separation is at most `D`, whether or not the separation has a minimum there.  The window is closed, and a one-sided minimum at either end counts: screening runs over consecutive windows, and an approach that peaks at the boundary of two windows must be reported by at least one of them.

Perturbations enter as a padding `P ≥ 0` in km.  The program screens the Kepler trajectories with the threshold `D + P`, and every theorem about trajectories holds for any pair of trajectories `ρ₁` and `ρ₂` that stay within `δ₁` and `δ₂` of the Kepler trajectories at every time of the window, with `δ₁ + δ₂ ≤ P`: such a pair at separation at most `D` puts the Kepler trajectories at most `D + P` apart.  The padding is the caller's premise.  No theorem bounds the distance of an SGP4 trajectory or of a true orbit from its Kepler trajectory, and that distance grows with the time from the epoch.  With `P = 0` and `ρₖ = rₖ`, the statements concern the model alone.

## Interface

The entry `screen` takes an array of 25 binary64 values and returns an array of binary64 values.

| Input index | Value | Requirement |
|---|---|---|
| 0 | Version | 1 |
| 1 to 7 | Object 1: `a`, `e`, `i`, `Ω`, `ω`, `M₀`, `τ` | `a > 0`, `0 ≤ e < 1` |
| 8 to 14 | Object 2, in the same order | `a > 0`, `0 ≤ e < 1` |
| 15 | `μ` | `μ > 0` |
| 16, 17 | `t₀`, `t₁` | `t₀ ≤ t₁` |
| 18, 19 | `D`, `P` | `D ≥ 0`, `P ≥ 0` |
| 20 | Apogee–perigee filter | 0 to skip, 1 to apply |
| 21, 22 | Orbit-path filter: levels `Lp` and cap `Cp` | Whole numbers, `0 ≤ Lp ≤ 40`, `1 ≤ Cp ≤ 2²⁰` |
| 23, 24 | Isolation: levels `L` and cap `C` | Whole numbers, `0 ≤ L ≤ 60`, `1 ≤ C ≤ 2²⁰` |

Every input must be finite, and the array must hold exactly 25 values.  An input that breaks a requirement gives status 4 and an output of five values.

| Output index | Value |
|---|---|
| 0 | Status |
| 1 | Number `K` of returned intervals |
| 2 | Verdict of the orbit-path filter |
| 3 | Number of cell tests of both searches |
| 4 | Number of isolation levels completed |
| 5 + 3j, 6 + 3j, 7 + 3j | Interval `j`: its ends `lo` and `hi` in minutes, and 1 when it is certain to hold a close approach, 0 otherwise |

| Status | Meaning |
|---|---|
| 0 | The isolation completed its `L` levels.  The intervals hold every close approach. |
| 1 | The apogee–perigee filter excluded the pair.  No interval is returned. |
| 2 | The orbit-path filter excluded the pair.  No interval is returned. |
| 3 | The isolation stopped at the cap `C`.  The intervals still hold every close approach, at a coarser resolution. |
| 4 | Invalid input. |

| Path verdict | Meaning |
|---|---|
| 0 | Not run: the apogee–perigee filter excluded the pair, or `Lp = 0` |
| 1 | Excluded |
| 2 | The paths come within `D + P` |
| 3 | Undecided after `Lp` levels |
| 4 | Stopped at the cap `Cp` |

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding.  It encloses the eccentric anomaly with `Demos.Sgp4.Kepler.rootI`, which bounds the distance from an approximate root by the residual over the least slope `1 − e`, and it encloses sines and cosines with the library's `sinI` and `cosI`.  The inputs are binary64 values, and the model takes their real values.

**Apogee–perigee filter.**  Every point of a path lies at a distance from the origin between the perigee radius `a (1 − e)` and the apogee radius `a (1 + e)`.  The filter excludes the pair when the computed lower bound of `a₂ (1 − e₂) − a₁ (1 + e₁)` or of `a₁ (1 − e₁) − a₂ (1 + e₂)` exceeds the computed upper bound of `D + P`.

**Orbit-path filter.**  A cell is a rectangle of eccentric anomalies `[α₁, β₁] × [α₂, β₂]`, and the search starts from the one cell `[0, 6.3] × [0, 6.3]`, which contains `[0, 2π]²`.  At each level, the filter first computes the separation of the two path points at the cell's computed center, and if its upper bound is at most the lower bound of `D + P` for some cell, it stops with verdict 2.  Otherwise it encloses each path over its side of each cell with interval sines and cosines and drops the cell when the lower bound of the squared distance between the two boxes exceeds the upper bound of `(D + P)²`.  It splits every other cell at its computed center into four.  When no cell remains, the verdict is 1.  When the new cells number more than `Cp`, the verdict is 4, and after `Lp` levels it is 3.

**Isolation.**  A cell is an interval of time `[α, β]` in minutes, and the search starts from `[t₀, t₁]`.  The cell test computes `m = α + (β − α) · 0.5` in binary64, encloses both positions at `m`, and computes a lower bound of `s(m)²` and an upper bound `ρ` of the distance from `m` to each end of the cell.  Each object moves at most `Vₖ = aₖ nₖ / (1 − eₖ)` km per minute, so the test drops the cell when the lower bound of `s(m)²` exceeds the upper bound of `(D + P + (V₁ + V₂) ρ)²`.  At each of `L` levels the isolation tests every cell, drops those that the test excludes, and splits the others at `m` into `[α, m]` and `[m, β]`.  When a level would leave more than `C` cells, the isolation keeps the cells of the previous level and stops with status 3.  A final pass tests the remaining cells, drops those it excludes, and marks a cell certain when `α ≤ m ≤ β` and the upper bound of `s(m)²` is at most the lower bound of `(D + P)²`.  Consecutive cells whose ends touch or overlap merge into one interval from the lesser start to the greater end, certain when one of them is.

The number of cell tests is at most `(L + 1) C` for the isolation and `2 Lp Cp` for the orbit-path filter, and the output holds at most `C` intervals.

## Theorems

Each theorem has a layer over the real numbers about the model, and a layer about the program that rests on the first through the interval enclosures.

| Code | Layer | Statement |
|---|---|---|
| M1 | Model | For `a > 0` and `0 ≤ e < 1`, `P` and `Q` are orthonormal, and `a (1 − e) ≤ \|p(E)\| ≤ a (1 + e)` for every `E`. |
| M2 | Model | `r(t) = p(E(t))` for every `t`, and `p(E + 2πk) = p(E)` for every integer `k`. |
| M3 | Model | `\|r(t) − r(t')\| ≤ (a n / (1 − e)) \|t − t'\|` for all `t` and `t'`. |
| F1 | Program | When the apogee–perigee filter excludes the pair, `s(t) > D + P` for every real `t`. |
| F2 | Program | When the orbit-path filter's verdict is 1, every point of one path lies farther than `D + P` from every point of the other, so `s(t) > D + P` for every real `t`.  Verdict 2 implies that some point of each path lies within `D + P` of the other. |
| I1 | Program | For status 0 or 3, every `t` in `[t₀, t₁]` with `s(t) ≤ D + P` lies in a returned interval. |
| I2 | Program | A returned interval marked certain contains a `t` with `s(t) ≤ D + P`. |
| S1 | Program | For every status other than 4, and for trajectories `ρ₁` and `ρ₂` within `δ₁` and `δ₂` of the Kepler trajectories on the window with `δ₁ + δ₂ ≤ P`, every `t` in `[t₀, t₁]` with `\|ρ₁(t) − ρ₂(t)\| ≤ D` lies in a returned interval, and none exists for status 1 or 2. |
| C1 | Compilation | The module's entry `screen`, called with the input array, returns the array of `screen` without a trap from a store with room for the allocation bound. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

An independent oracle in Python propagates both Kepler orbits with its own solver of Kepler's equation in multiple precision, samples the separation over the window at a step well below the duration of the shortest close approach, and refines each sampled local minimum.  The test requires every sampled time with `s ≤ D + P`, and every refined minimum at most `D + P`, to lie in a returned interval, every certain interval to hold such a time, and every excluded pair to have a sampled and refined minimum above `D + P`.  For the orbit-path filter, the oracle samples the two paths over a grid of eccentric anomalies and refines the closest pairs.  The cases include constructed pairs with a known miss distance below, at, and above `D`, approaches whose minimum falls before `t₀` or after `t₁` with the separation below `D` at the end, nearly coplanar orbits, eccentric orbits, pairs that each filter excludes and pairs it must keep, and windows of one day and one week.  The tests measure the cost of a pair: the cell tests, the levels, and the time in the WebAssembly module.  A module test compares the WebAssembly module with native Lean on generated inputs, bit for bit.

## What lies outside the theorems

The theorems concern Kepler trajectories, or trajectories within the padding of them by the caller's premise.  The choice of `D`, `P`, and the frame, and the relation of the elements to the objects, are the caller's.  The theorems bound no width and no count: a coarse result is sound, and the number of intervals and their lengths depend on `L`, `C`, and the arithmetic.  The orbit-path filter's verdicts 3 and 4 and the isolation's status 3 carry no statement beyond I1.  The filters exclude a pair for all time, and the window enters only the isolation.
