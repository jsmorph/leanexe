# Event windows requirements

## Purpose and scope

The program finds the times of a window at which a condition on a spacecraft's position and the Sun's direction holds, and it misses none of them.  For a Kepler orbit, a window of time, and one event, it returns intervals of time, called runs, that hold every time of the window at which the event's condition holds, and it labels a run 1 when the condition holds at every time of it.  The events of this iteration need no rotation of the Earth: the spacecraft in the Earth's shadow, and a vector fixed in the inertial frame or in the spacecraft's radial, along-track, and cross-track frame within an exclusion angle of the Sun.  Ground stations and targets on the Earth need the frames candidate (5.2) and come in a later iteration.

The program is a ground program compiled to WebAssembly, in the verified compiler's dialect of `UInt64` and binary64 values with bounded loops.  Its uses are the planning of power and thermal loads around eclipses, and the planning of attitudes and instrument times around the Sun's exclusion from a sensor's field of view.  Brief 5.1 asks whether the output should feed the slew planner, for example as the window of validity of a cone set, and this iteration leaves that link out.

## Form of the theorem

Brief 5.1 states two properties of the returned intervals: outside them the condition is false at every instant of the window, and each of them contains a crossing.  The two conflict.  Intervals that cover the times at which the condition holds contain no crossing when the condition holds over the whole window, and intervals that enclose the crossings leave out the times between an entry and an exit.  The theorem of this program takes the first form: the runs cover every time of the window at which the condition holds.  It adds a second statement that places the crossings: at every time of a run labeled 1 the condition holds.  A crossing is a time of the window with times of the window arbitrarily close to it at which the condition holds and at which it fails, and every crossing therefore lies in a returned run and inside no run labeled 1 except at its ends.  An eclipse that begins and ends inside the window typically appears as a run labeled 0 that holds the entry, a run labeled 1, and a run labeled 0 that holds the exit, and a run labeled 0 brackets a crossing to its length.

## Trajectory model

The trajectory is two-body motion, with the Kepler pieces of [the screening demo](../Screening/README.md), for four reasons.  The isolation excludes an interval of time by a bound on the rate of change of the condition, and Kepler's equation gives the bound on the speed `a n / (1 − e)` by algebra (`Demos.Screening.position_lipschitz`).  The enclosure of the eccentric anomaly, the position's interval program, and their theorems exist (`Demos.Screening.kepler.encloses`, `Demos.Screening.positionAt_encl`).  The body-fixed vectors need the direction of the position and the orbit normal, which the Kepler orbit gives as a function of time.  SGP4's box theorem holds over an interval of time, but SGP4's velocity output is not the derivative of its position, so a rate bound would rest on boxes over each cell of time, whose widths grow at 1.2 to 2.7 times the sampled range of the position (the measurement in [the screening requirements](../Screening/requirements.md#prerequisite-sgp4-boxes-over-an-interval-of-time)).  SGP4 trajectories enter the shadow event through a padding input, as they enter the screening demo.

An orbit has the semimajor axis `a` in km, the eccentricity `e`, the inclination `i`, the right ascension of the ascending node `Ω`, the argument of perigee `ω`, and the mean anomaly `M₀` in degrees at its epoch `τ` in minutes.  With the gravitational parameter `μ` in km³/s², the mean motion is `n = 60 √(μ / a³)` radians per minute, the eccentric anomaly `E(t)` is the root of `E − e sin E = M₀ π/180 + n (t − τ)`, and the position in km is `r(t) = a (cos E − e) p̂ + a √(1 − e²) sin E q̂`, with `p̂` and `q̂` the unit vectors toward the perigee and a quarter turn ahead of it.  These are the definitions of `Demos.Screening.Orbit.position`, which the program reuses by import.

## The Sun's direction

The model of the Sun's direction is the U.S. Naval Observatory's algorithm for approximate solar coordinates.  For `D` days from J2000.0, the Julian date 2451545.0, with every angle in degrees,

```text
g = 357.529 + 0.98560028 D          mean anomaly
q = 280.459 + 0.98564736 D          mean longitude
λ = q + 1.915 sin g + 0.020 sin 2g  apparent ecliptic longitude
ε = 23.439 − 0.00000036 D           mean obliquity of the ecliptic
ŝ = (cos λ, cos ε sin λ, sin ε sin λ)
```

and `ŝ` is the geocentric unit vector toward the Sun in the equatorial frame, the ecliptic latitude taken as zero.  The constants are the decimal numbers as written, which the program encloses by exact ratios of integers, so the theorems concern the formula with its published constants.  The time of the window is in minutes on one scale with the orbit's epoch, and minute 0 falls `d₀` days from J2000.0, so `D(t) = d₀ + t/1440`.  The program evaluates the formula with no reduction of the angles, which the periodicity of `sin` and `cos` makes unnecessary.

The accuracy of the formula and the frame of the elements are premises outside the theorems.  The USNO states an accuracy of about 1′ within two centuries of 2000, that is for `|D| ≤ 73,050`, against the JPL ephemeris DE405, and takes the Julian date as a form of Universal Time.  The formula gives the apparent longitude with the mean obliquity and no nutation, so its frame is closest to the mean equator and equinox of date, and the elements must refer to that frame.  TEME, the frame of SGP4, differs from it by the nutation of the equator, at most about 10″, and from the true equator and equinox of date by the equation of the equinoxes, at most about 17″.  The J2000 frame differs from it by precession, 0.363° on 2026-01-01 and 0.377° on 2026-12-31, which a caller with J2000 elements applies.  For the shadow, the formula's apparent direction is the direction of the light that casts the shadow, about 20.5″ from the geometric line through the two centers.

The exclusion events use the geocentric direction.  The direction from the spacecraft differs from it by at most `arcsin(a (1 + e) / d)` for a Sun at distance `d`, which for `a (1 + e) ≤ 42,164` km and `d ≥ 1.47 · 10⁸` km is below 0.017°.  A caller who needs the direction from the spacecraft, the formula's accuracy, and the frame's offset to hold for the cover adds these angles to `β`, and subtracts them from `β` for the statement about runs labeled 1.  For the shadow, an error of angle `θ` in `ŝ` is a rotation, which moves `x` and `y` as a displacement of the position by at most `a (1 + e) θ`, so a padding `P ≥ δ + a (1 + e) θ` carries the formula's error into the theorems of the padding, 2.0 km for a low orbit and 12.3 km at the geostationary radius for `θ = 1′`.

The rate of `ŝ` follows from the formula.  `λ` changes by at most `0.98564736 + (1.915 + 2 · 0.020) · 0.98560028 · π/180` degrees per day, about 1.01928, since `|sin x − sin y| ≤ |x − y|`, and `ε` by `0.00000036`.  A unit vector `(cos λ, cos ε sin λ, sin ε sin λ)` moves by at most `|Δλ| + |Δε|` radians, so `|ŝ(D) − ŝ(D′)| ≤ ω_d |D − D′|` with `ω_d = π/180 · (0.98564736 + 1.955 · 0.98560028 · π/180 + 0.00000036)` per day, and the program divides it by 1440 for a rate per minute.

## Events

### Shadow

The shadow model is conical.  The Earth is a sphere of radius `R`, and the Sun's light is bounded by a cone about the shadow axis, the line through the Earth's center along `−ŝ`, with a half-angle `α` that the caller gives in degrees.  With `x = −r · ŝ`, the distance of the spacecraft behind the plane through the Earth's center normal to `ŝ`, and `y = |r × ŝ|`, its distance from the shadow axis, the spacecraft is in the shadow at time `t` when

`x ≥ 0` and `y cos α − x sin α ≤ R`.

A positive `α` gives the penumbral cone, whose apex lies `R / sin α` from the Earth's center toward the Sun, and the condition then holds for a spacecraft that the Earth hides from part or all of the Sun.  A negative `α` gives the umbral cone, whose apex lies `R / sin |α|` behind the Earth, and the condition holds where the Earth hides all of the Sun.  `α = 0` gives the cylindrical model.  For a Sun of radius `R☉` at distance `d`, the tangent cones of the two spheres have `sin α = (R☉ + R) / d` for the penumbra and `sin |α| = (R☉ − R) / d` for the umbra, 0.26890° and 0.26401° at 1 AU.  From aphelion to perihelion the penumbral angle runs from 0.26448° to 0.27347° and the umbral angle from 0.25967° to 0.26850°, and the caller chooses the angle.  The penumbral cone grows with `α`, so the angle at perihelion covers every date for the cover and the angle at aphelion serves the statement about runs labeled 1.  The umbral cone shrinks as `|α|` grows, beyond about 30 km behind the Earth, so the angle at aphelion covers every date for the cover and the angle at perihelion serves the runs labeled 1.  The conditions describe the shading of the two spheres except in a shell within `R (1/cos α − 1)`, about 70 m, of the Earth's surface.  The model treats the Earth as a sphere without an atmosphere, and the choice of `R`, which may include a margin for the Earth's flattening and the atmosphere, is the caller's.

Perturbations enter as a padding `P ≥ 0` in km.  For a trajectory `ρ` that stays within `δ ≤ P` of the Kepler trajectory at every time of the window, `x` and `y` of `ρ` differ from those of `r` by at most `δ`.  The program tests the Kepler trajectory with margins that make the theorems hold for every such `ρ`: the runs cover every time at which `ρ` is in the shadow, and `ρ` is in the shadow at every time of a run labeled 1.  With `P = 0` the statements concern the Kepler trajectory.  The padding is the caller's premise, since no theorem bounds the distance of an SGP4 trajectory or a true orbit from its Kepler trajectory.

### Exclusion of the Sun

A vector `b` is within the exclusion angle `β` of the Sun at time `t` when the angle between `v(t)` and `ŝ(t)` is at most `β`, that is, when `|v(t)| |ŝ(t)| cos β ≤ v(t) · ŝ(t)`, for `0° ≤ β ≤ 180°` and `b ≠ 0`.  The vector is either fixed in the inertial frame, `v(t) = b`, or fixed in the frame of the orbit's radial, along-track, and cross-track directions, `v(t) = b₁ R̂(t) + b₂ Ŝ(t) + b₃ Ŵ`, with

`R̂ = r / |r|`, `Ŵ = p̂ × q̂`, `Ŝ = Ŵ × R̂`.

`Ŵ` is the orbit normal along the angular momentum, and `Ŝ` lies in the orbit plane a quarter turn ahead of `R̂`, so a spacecraft that holds an attitude fixed in that frame, such as a nadir-pointing spacecraft, has its body vectors fixed in it.  A spacecraft that holds an inertial attitude has its body vectors fixed in the inertial frame, and the caller gives them in that frame.  The frame `(R̂, Ŝ, Ŵ)` is orthonormal, so `|v(t)| = |b|`.  The exclusion events have no padding: the inertial event does not depend on the position, and a bound on the distance of a trajectory from the Kepler trajectory bounds no error of the orbit's frame, so the theorems of the frame event concern the Kepler trajectory.

## Rate bounds

Each event's condition is `g₁(t) ≤ 0` and `g₂(t) ≤ 0` for two real functions, each with a bound `Lₖ` on its rate, `|gₖ(t) − gₖ(t′)| ≤ Lₖ |t − t′|`, in units per minute, and a margin `Wₖ` for the padding.  `V = a n / (1 − e)` bounds the speed in km per minute (M3 of the screening demo), `r⁺ = a (1 + e)` the distance from the Earth's center, and `ω = ω_d / 1440` the rate of `ŝ` in radians per minute.

| Event | `g₁` | `g₂` | Rate bounds | Margins |
|---|---|---|---|---|
| Shadow | `r · ŝ` | `y cos α + (r · ŝ) sin α − R` | `L₁ = V + r⁺ ω`, `L₂ = (\|cos α\| + \|sin α\|) L₁` | `W₁ = P`, `W₂ = (\|cos α\| + \|sin α\|) P` |
| Inertial vector | `\|b\| cos β − b · ŝ` | `g₁` | `\|b\| ω` | 0 |
| Vector in the orbit's frame | `\|b\| cos β − v · ŝ` | `g₁` | `(\|b₁\| + \|b₂\|) V / (a (1 − e)) + \|b\| ω` | 0 |

The rate of `r · ŝ` and of `y` is at most `|ṙ| + |r| |ŝ̇|`, and the shadow's second function takes `|cos α|` of the first and `|sin α|` of the second.  The factor `|cos α| + |sin α|` is loose by up to `√2`: the map from `r` to `(x, y)` moves no farther than `r`, so `L₁` and `P` also serve `g₂`, but the factor follows from the two rates by the triangle inequality alone.  For the vector in the orbit's frame, `|R̂(t) − R̂(t′)| ≤ |r(t) − r(t′)| / (a (1 − e))`, since the radius is at least `a (1 − e)`, and `Ŝ` moves as `R̂` does, so `v` moves at most `(|b₁| + |b₂|) V / (a (1 − e))` per minute.  A trajectory `ρ` within `δ ≤ P` of `r` has functions `h₁` and `h₂` with `|hₖ − gₖ| ≤ Wₖ`.

## Interface

The entry `events` takes an array of 21 binary64 values and returns an array of binary64 values.

| Input index | Value | Requirement |
|---|---|---|
| 0 | Version | 1 |
| 1 to 7 | Orbit: `a`, `e`, `i`, `Ω`, `ω`, `M₀`, `τ` | `a > 0`, `0 ≤ e < 1`, for every event |
| 8 | `μ` | `μ > 0`, for every event |
| 9 | `d₀`, days from J2000.0 at minute 0 | `\|d₀\| ≤ 10⁶` |
| 10, 11 | `t₀`, `t₁` in minutes | `−10⁹ ≤ t₀ ≤ t₁ ≤ 10⁹` |
| 12 | Event | 1 shadow, 2 inertial vector, 3 vector in the orbit's frame |
| 13 | Angle in degrees: `α` for the shadow, `β` for a vector | `−90 < α < 90`, `0 ≤ β ≤ 180` |
| 14 | `R` in km, for the shadow | `R > 0` for event 1 |
| 15 | `P` in km, for the shadow | `P ≥ 0` for event 1 |
| 16 to 18 | `b`, for a vector | Not all zero for events 2 and 3 |
| 19, 20 | Levels `N` and cap `C` | Whole numbers, `0 ≤ N ≤ 60`, `1 ≤ C ≤ 2²⁰` |

Every input must be finite, and the array must hold exactly 21 values.  The orbit's requirements hold for every event, including the inertial vector, which does not use the orbit, and the entries 14 to 18 that an event does not use are otherwise free.  An input that breaks a requirement gives the output `2, 0, 0, 0`.

| Output index | Value |
|---|---|
| 0 | Status: 0 when the isolation completed its `N` levels, 1 when it stopped before a level of more than `C` cells, 2 for an invalid input |
| 1 | Number `K` of runs |
| 2 | Number of cell tests |
| 3 | Number of levels completed |
| 4 + 3j, 5 + 3j, 6 + 3j | Run `j`: its ends in minutes, and its label, 1 when the condition holds at every time of it and 0 otherwise |

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding, with the eccentric anomaly enclosed by `Demos.Screening.keplerI` and sines and cosines by the library's `sinI` and `cosI`.  The model takes the real values of the binary64 inputs.  An interval operation rejects on overflow, on a divisor that the arithmetic cannot show nonzero, and on a square-root operand that it cannot show nonnegative, and a test whose intervals are rejected excludes nothing and labels nothing, so a rejection only keeps cells.

A cell is an interval of time `[c₀, c₁]` in minutes, and the search starts from `[t₀, t₁]`.  The cell test computes `m = c₀ + (c₁ − c₀) · 0.5` in binary64, encloses `g₁(m)` and `g₂(m)`, and computes an upper bound `η` of the distance from `m` to each end of the cell.  It excludes the cell when, for some `k`, the lower bound of `gₖ(m)` exceeds the upper bound of `Lₖ η + Wₖ`, since then `hₖ > 0` at every time of the cell.  It marks the cell whole when, for both `k`, the upper bound of `gₖ(m) + Lₖ η + Wₖ` is at most 0, since then `hₖ ≤ 0` at every time of the cell.

At each of `N` levels the isolation tests every cell and drops those that the test excludes.  It splits a kept cell at `m` into `[c₀, m]` and `[m, c₁]` when the cell is not marked whole and `c₀ < m < c₁`, and otherwise keeps it unsplit.  When a level would leave more than `C` cells, the isolation keeps the cells of the previous level and stops with status 1.  A final pass tests the remaining cells, drops those it excludes, and gives each kept cell the label 1 when it is marked whole and 0 otherwise.  A cell merges into the run before it when the two labels agree and the cell's start lies between the run's ends, and the run then ends at the greater of the two ends.

The cells stay in increasing order of time, so the runs do, and two consecutive runs with equal labels do not touch.  The tests check both properties, and no theorem states them.  The number of cell tests is at most `(N + 1) C`, and the output holds at most `C` runs.  A level stores at most `2C` new cells of 16 bytes before the test against the cap, and the output takes `8 (5 + 3K)` bytes with its length.  The call theorem states the generated allocation bound.

## Theorems

Each theorem has a layer over the real numbers about the model and a layer about the program that rests on it through the interval enclosures.  The condition of an input is the condition of its event for the Kepler trajectory, and for the shadow with `P > 0` E4 states the theorems for the trajectories within the padding.

| Code | Layer | Statement |
|---|---|---|
| M1 | Model | `\|ŝ(D)\| = 1` and `\|ŝ(D) − ŝ(D′)\| ≤ ω_d \|D − D′\|`. |
| M2 | Model | `x² + y² = \|r\|²`, so `y` is the distance from the shadow axis, and for the orbit's frame `\|v(t)\| = \|b\|`. |
| M3 | Model | Each `gₖ` of each event satisfies `\|gₖ(t) − gₖ(t′)\| ≤ Lₖ \|t − t′\|`. |
| E1 | Program | For a valid input, every `t` in `[t₀, t₁]` at which the condition holds lies in a returned run. |
| E2 | Program | For a valid input, the condition holds at every time of a run labeled 1. |
| E3 | Program | For a valid input, every run lies in `[t₀, t₁]`. |
| E4 | Program | For the shadow and a trajectory `ρ` within `δ ≤ P` of the Kepler trajectory on the window, E1 and E2 hold for the shadow condition of `ρ`. |
| E5 | Program | For a valid input, every crossing of the window lies in a returned run, and a crossing in a run labeled 1 is one of its ends. |
| E6 | Program | For a valid input, the status is 0 or 1, outputs 0 and 3 are the search's status and levels, status 0 comes with all `N` levels, and status 1 with fewer levels and a next level of more than `C` cells. |
| C1 | Compilation | The module's entry `events`, called with the input array, returns the array of `events` without a trap from a store with room for the generated allocation bound. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  E1 to E6 also hold for an output that labels every run 0 or returns the whole window as one run.  The program's text, which C1 ties to the module, fixes the method, and the tests check that the output follows it.

## Tests

An oracle in Python, written apart from the program, evaluates the model with its own solver of Kepler's equation, its own evaluation of the Sun's formula, and each event's functions as this document states them.  It samples the window in binary64 at a step of `10⁻³` minutes, `10⁻²` minutes for the inertial vector, with both ends among the samples.  It evaluates in mpmath at 30 digits every sample whose `g₁` or `g₂` lies within `10⁻⁷` of zero, and it refines each change of the condition between two samples by bisection in mpmath to `10⁻¹⁰` minutes, which gives a time at which the condition holds and a time at which it fails.  A sample whose `gₖ` lies within `10⁻¹²` of zero in mpmath counts as inconclusive.

The test requires:

- status 2 and the output `2, 0, 0, 0` exactly for the invalid inputs;
- for valid inputs, the status each case states, `4 + 3K` values, labels 0 and 1, at most `C` runs, at most `(N + 1) C` cell tests, `N` levels completed at status 0 and fewer at status 1, runs in increasing order inside `[t₀, t₁]`, and no two consecutive runs with equal labels that touch;
- every sampled time and every refined time at which the condition holds to lie in a returned run, and every sampled time and every refined time at which the condition fails to lie in no run labeled 1.

For the shadow with `P > 0`, the oracle also tests the trajectories displaced from the Kepler trajectory by `P` along the gradient of `g₂` and along `ŝ`, toward and away from the shadow.  The test also checks that the output follows the method where the margins far exceed rounding.  For status 0 after 18 levels or more, with `Δ = max((t₁ − t₀) / 2^N, 10⁻⁹)` minutes, every sampled time at which `gₖ + Lₖ Δ + Wₖ < 0` for both `k` must lie in a run labeled 1, and every sampled time in a returned run must have `gₖ ≤ Lₖ Δ + Wₖ` for both `k`.  The floor `10⁻⁹` minutes exceeds by 30 times the band, about `3 · 10⁻¹¹` minutes at a low orbit's crossings, in which the width of the enclosures keeps a cell from both the exclusion and the mark.  A mutation run alters correct outputs so that each alteration is wrong: it removes the run that holds the most samples of the condition, moves the start of a run past a refined time of the condition, labels 1 a run that holds a refined time at which the condition fails, reports status 2, and returns the whole window as one run labeled 1 or 0.  The test must fail on each.

The cases include an eclipse of a low orbit with the Sun near the orbit plane, a low orbit with the Sun near the orbit normal and no eclipse, a geostationary orbit near an equinox with an eclipse and near a solstice without one, an eccentric orbit, the penumbral, umbral, and cylindrical cones, a padding, a window that begins or ends in the shadow, grazing passes, an Earth radius above the perigee radius, a circular orbit at 200,000 km whose rate at its crossings lies between `V` and `L₁`, an inertial vector whose angle to the Sun crosses `β` over a week, a vector in the orbit's frame with an exclusion every orbit, a cross-track vector whose angle crosses `β` over two days, a vector in the frame of an eccentric orbit with a crossing near perigee, `N = 0`, `C = 1` and `C = 64` at `N = 20`, `N = 40`, enclosures that reject, and invalid inputs.  The tests measure the cell tests and the time of a call in the WebAssembly module.  A module test compares the WebAssembly module with native Lean on generated inputs, bit for bit.

## What lies outside the theorems

The theorems concern the stated model: Kepler motion, the USNO's formula for the Sun's direction, a spherical Earth with a shadow cone of fixed half-angle, and an attitude fixed in the inertial frame or in the orbit's frame.  The accuracy of the formula, the frame of the elements, the parallax of the Sun for the exclusion events, the cone's half-angle, `R`, and `P` are the caller's premises.  The theorems bound no width and no count: a coarse result is sound, and the number and lengths of the runs depend on `N`, `C`, and the rounding.  Status 1 carries E1 to E5 at a coarser resolution.  E5 concerns the Kepler trajectory, since a trajectory within the padding need not be continuous.

## References

- [U.S. Naval Observatory, Approximate solar coordinates](https://aa.usno.navy.mil/faq/sun_approx)
- [The conjunction screening demo](../Screening/README.md)
- [The interval library](../../Library/Numerics/Interval/README.md)
