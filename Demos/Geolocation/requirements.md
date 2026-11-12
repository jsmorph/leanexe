# Emitter geolocation requirements

## Purpose and scope

The program locates a radio emitter from time differences and frequency differences of arrival at several receivers, with bounded measurement errors.  It returns boxes of geodetic coordinates that contain every emitter position consistent with the measurements, within the stated error bounds, and for receiver states anywhere in their stated intervals.  The search is an interval branch-and-prune: a box is discarded only when interval evaluation shows that no point of it fits the measurements.  A second label marks the boxes in which every point fits, so the result also certifies positions that the measurements cannot exclude.

Its uses are the location of distress beacons, as the medium-altitude system of Cospas-Sarsat (MEOSAR) does with these two measurement types, and the location of sources of radio interference.  The program is a ground program compiled to WebAssembly by the verified compiler, in its dialect of `UInt64` and binary64 values with bounded loops.  Receiver states and their error bounds come from the caller: from an ephemeris in the Earth-fixed frame, or in the TEME frame of SGP4 at the time of each receiver, which the program rotates into the Earth-fixed frame with the sidereal time and polar motion of [the frames and time demo](../Frames/README.md).

The theorems concern a stated measurement model.  Light time, the rotation of the Earth during the light time, atmospheric delays, relativistic terms, the motion of the emitter, and the conversion of the measurements from a ground station to the receivers lie outside it, and [the section on the model's limits](#what-the-model-leaves-out) gives their sizes so that the caller can add them to the error bounds.  Existence or uniqueness of a solution within a box, by a Krawczyk test, is left for a later iteration.

## The emitter

The emitter is fixed on the rotating Earth at the position with geodetic latitude `φ`, longitude `λ`, and height `h` on the WGS 84 ellipsoid, `x = P(φ, λ, h)`, where `P` is `Demos.Frames.Model.position` of the frames demo:

`P(φ, λ, h) = ((N + h) cos φ cos λ, (N + h) cos φ sin λ, (N (1 − e²) + h) sin φ)`,  `N = a / √(1 − e² sin² φ)`,

with `a = 6378.137` km and `e² = f (2 − f)` for the flattening `f = 1/298.257223563`.  The caller gives a search region `[φ₀, φ₁] × [λ₀, λ₁] × [h₀, h₁]` of coordinates in radians and km.  An emitter on the ellipsoid has `h₀ = h₁ = 0`, an emitter on land a range of terrain heights such as `[−0.5, 9]` km, and an emitter on an aircraft a range up to its ceiling.  The region `[−1.5707963267948968, 1.5707963267948968] × [−3.1415926535897936, 3.1415926535897936] × [h₀, h₁]`, whose bounds are the binary64 values just beyond `±π/2` and `±π`, holds geodetic coordinates of every point whose geodetic height lies in `[h₀, h₁]`.  The theorems state their results for coordinate triples of the region, and by `P` for the Earth-fixed points of those triples.

## Measurement model

A receiver `i` has the Earth-fixed position `sᵢ` in km and velocity `uᵢ` in km/s, the velocity relative to the rotating Earth.  With `ρᵢ(x) = √((sᵢ,₁ − x₁)² + (sᵢ,₂ − x₂)² + (sᵢ,₃ − x₃)²)`, the Euclidean distance, and the speed of light `c = 299792.458` km/s, the model of each measurement is

| Measurement | Model at the emitter position `x` | Unit |
|---|---|---|
| Time difference of arrival `τᵢⱼ`, the arrival time at `i` less that at `j` | `(ρᵢ(x) − ρⱼ(x)) / c` | s |
| Frequency difference of arrival `νᵢⱼ`, the received frequency at `i` less that at `j` | `−f₀ (ρ̇ᵢ(x) − ρ̇ⱼ(x)) / c` | Hz |

with the range rate `ρ̇ᵢ(x) = (sᵢ − x) · uᵢ / ρᵢ(x)` and the emitted carrier frequency `f₀` in Hz.  The range rate is the time derivative of `ρᵢ` along the receiver's motion for an emitter fixed in the Earth-fixed frame (theorem M1), so the frequency model is the first-order Doppler shift `f₀ (1 − ρ̇ᵢ/c)` received at `i`, less that at `j`.  At `x = sᵢ` the range rate divides by zero, and the model takes the value 0 of Lean's division there.  The program's division rejects at such points, so a box that holds a receiver's position is kept.  The carrier frequency is unknown within an interval `[f_lo, f_hi]` that the caller gives: the 406 MHz beacons of Cospas-Sarsat transmit in the band from 406.0 to 406.1 MHz, and an uncertainty of `2.5·10⁻⁴` in `f₀` changes a frequency difference of 10 kHz by 2.5 Hz.

A measurement `k` names two distinct receivers `i` and `j`, a measured value `yₖ`, and a bound `εₖ ≥ 0`.  An emitter position `x` fits the measurements for receiver states `(sᵢ, uᵢ)` and a carrier frequency `f₀` when `|mₖ(x) − yₖ| ≤ εₖ` for every measurement `k`, where `mₖ` is the model of the measurement's kind.  The position is consistent with the measurements when it fits them for some admissible parameter: admissible receiver states and some `f₀` in `[f_lo, f_hi]`.

## Receiver states

The caller gives each receiver's state as six intervals, one per component of its position and velocity, and the admissible states are those whose components lie in the intervals.  An exact state is an interval of zero width.  The frame `F` of the input fixes how the intervals give the Earth-fixed states.

**Earth-fixed input (`F = 0`).**  The intervals hold the components of `sᵢ` and `uᵢ` in the Earth-fixed frame, as GNSS broadcast ephemerides give them: WGS 84 or the ITRF, with the velocity relative to the rotating Earth.

**TEME input (`F = 1`).**  The intervals hold the components of the position `rᵢ` and velocity `vᵢ` in the TEME frame of SGP4, and a further interval holds the time `tᵢ` of the state in seconds of UT1 from the start of the day `d`, a Modified Julian Date.  Intervals `xp` and `yp` of polar motion in arcseconds hold for all receivers.  With the rotation `E(θ) = R1(−yp) R2(−xp) R3(θ)` of `Demos.Frames.Model.earthFixed` and the sidereal angle `θ(t) = gmst82(julian(d, t))` of `Demos.Frames.Model`, the Earth-fixed state is

`sᵢ = E(θ(tᵢ)) rᵢ`,  `uᵢ = E(θ(tᵢ)) (vᵢ + ω(tᵢ) (rᵢ,₂, −rᵢ,₁, 0))`,

where `ω(t)` is the derivative of `θ` with respect to `t`,

`ω(t) = (π/43200) (1 + (8640184.812866 + T (2 · 0.093104 − 3 · 6.2·10⁻⁶ T)) / 3155760000)`,  `T = (d − 51544.5 + t/86400) / 36525`,

about `7.2921158·10⁻⁵` rad/s.  The added vector `ω (r₂, −r₁, 0)` is `−ω ẑ × r` in TEME coordinates, and `R3(θ)` carries it to `−ω ẑ × R3(θ) r`, so `uᵢ` is the frames demo's rotation of the velocity relative to the rotating Earth.  Theorem M2 states that `uᵢ` is the derivative of `E(θ(t)) r(t)` at `tᵢ` for a TEME trajectory `r` with `r(tᵢ) = rᵢ` and `r′(tᵢ) = vᵢ`, with polar motion constant over the time.  This is the transformation of the function `teme2ecef` of Vallado's SGP4 code, with the order of the polar-motion rotations of the frames demo and `ω` derived from GMST 1982, which differs from that code's constant `7.29211514670698·10⁻⁵` rad/s by `7·10⁻¹²` rad/s, or `2·10⁻⁷` km/s at 29,600 km.  The rate is per second of UT1, which differs from the SI second by the excess length of day, about `10⁻⁸` relative.  An admissible state of a receiver has `tᵢ`, `rᵢ`, and `vᵢ` in their intervals, and `xp` and `yp`, one value for all receivers, in theirs.

## What the model leaves out

The model takes each receiver's state at the time of arrival at that receiver and the emitter fixed in the Earth-fixed frame, and it uses the instantaneous distance.  The signal travels in an inertial frame, and during the light time `L/c` the Earth turns by `ω L/c`, which moves the emitter by at most `ω L p / c` for its distance `p` from the polar axis and changes the path length by no more.  For `p ≤ 6378` km this is 45 m, or 0.15 μs, at a range of 28,900 km, the largest range from the nominal Galileo orbit to the Earth's surface, 49 m at 31,642 km for Galileo satellites 5 and 6, whose orbit reaches 25,900 km altitude, and 4.7 m at 3,000 km.  A time difference therefore differs from the model by up to twice the larger of the two receivers' amounts, and the caller adds this to `εₖ`.  The ionosphere delays a signal by `40.3 · TEC / f₀²` m for a total electron content `TEC` in electrons per m², about 122 m, or 0.41 μs, at 406 MHz for 50 TEC units along the path, and the troposphere by about 2.4 m at the zenith and more at low elevation.  Only the difference between the two paths enters a time difference.

The frequency model is the first-order Doppler shift for an emitter at rest on the Earth.  Terms of second order in `v/c`, for a receiver speed `v` relative to an inertial frame, amount to about `f₀ (v/c)²`: 0.07 Hz at 406 MHz for 3.9 km/s, the speed of a MEOSAR satellite, and 0.25 Hz for 7.5 km/s in a low orbit.  The difference of gravitational potential between the emitter and a receiver shifts the frequency by up to about 0.22 Hz at 406 MHz for a receiver at 29,600 km from the Earth's center, and it cancels in a difference between receivers at equal distances.  An emitter that moves at speed `w` relative to the Earth shifts each received frequency by up to `f₀ w / c` and a difference by up to twice that: 339 Hz and 677 Hz at 406 MHz for an aircraft at 0.25 km/s.  For such an emitter the caller adds that amount to `εₖ` or uses time differences alone.  Drift of the emitter's carrier during the measurements, the receivers' clock and frequency errors, and the conversion of times and frequencies measured at a ground station through a transponder to the receivers are the caller's, and each enters `εₖ`, `[f_lo, f_hi]`, or the receivers' intervals.

## Interface

The entry `locate` takes an array of binary64 values and returns an array of binary64 values.  For `n` receivers and `m` measurements the input holds exactly `20 + 14 n + 5 m` values, every value finite.  An interval is given as two values `lo ≤ hi` and stands for every real number between them.

| Input index | Value | Requirement |
|---|---|---|
| 0 | Version | 1 |
| 1 | Frame `F` of the receivers' states | 0 Earth-fixed, 1 TEME |
| 2 | Number of receivers `n` | Whole, `2 ≤ n ≤ 16` |
| 3 | Number of measurements `m` | Whole, `1 ≤ m ≤ 64` |
| 4 | Day `d`, a Modified Julian Date, for `F = 1` | Whole, `0 ≤ d < 2³²` |
| 5, 6 | Interval of `xp` in arcseconds, for `F = 1` | Ordered |
| 7, 8 | Interval of `yp` in arcseconds, for `F = 1` | Ordered |
| 9, 10 | Interval `[f_lo, f_hi]` of the carrier frequency in Hz | `0 < f_lo ≤ f_hi` |
| 11, 12 | `φ₀`, `φ₁` in radians | Ordered |
| 13, 14 | `λ₀`, `λ₁` in radians | Ordered |
| 15, 16 | `h₀`, `h₁` in km | Ordered |
| 17 | Resolution `r` in km | `r > 0` |
| 18 | Levels `N` | Whole, `0 ≤ N ≤ 128` |
| 19 | Cap `C` on the number of boxes | Whole, `1 ≤ C ≤ 65536` |
| `20 + 14 i` to `33 + 14 i` | Receiver `i`: intervals of `tᵢ` (s, for `F = 1`), of the three components of position (km), and of the three components of velocity (km/s) | Each ordered |
| `20 + 14 n + 5 k` to `24 + 14 n + 5 k` | Measurement `k`: its kind, 1 for a time difference and 2 for a frequency difference, the receivers `i` and `j`, the value `yₖ` (s or Hz), and the bound `εₖ` | Kind 1 or 2; `i` and `j` whole with `0 ≤ i, j < n` and `i ≠ j`; `εₖ ≥ 0` |

The entries that the frame does not use, the day and polar motion for `F = 0` and the receivers' times for `F = 0`, must still meet their requirements.  An input that breaks a requirement gives the output `3, 0, 0, 0`.

| Output index | Value |
|---|---|
| 0 | Status: 0 complete, 1 stopped at the cap, 2 stopped after `N` levels, 3 invalid input, 4 receiver states that the interval arithmetic rejects |
| 1 | Number `K` of boxes |
| 2 | Number of box tests |
| 3 | Number of levels completed |
| `4 + 7 j` to `10 + 7 j` | Box `j`: `φ` from, `φ` to, `λ` from, `λ` to, `h` from, `h` to, and its label, 1 when every point of the box fits the measurements for every admissible parameter, and 0 otherwise |

Status 4 occurs when an interval of a receiver's Earth-fixed state is rejected, as on overflow, and its output is `4, 0, 0, 0`.  For `F = 0` the input's intervals are the states, so status 4 does not occur.

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding.  The model takes the real values of the binary64 inputs, and each decimal constant, such as `c`, enters as the interval of an exact ratio of integers.  It first encloses the Earth-fixed state of each receiver: for `F = 0` the input's intervals, and for `F = 1` the frames demo's `angleWith` and `toEarthI` applied to the TEME intervals at the interval of `tᵢ`, and to the velocity term with an enclosure of `ω(tᵢ)`.  It encloses the carrier frequency by `[f_lo, f_hi]`.  An interval operation rejects on overflow, on a divisor that the arithmetic cannot show nonzero, and on a square-root operand whose lower end is negative.

A box is a triple of intervals of latitude, longitude, and height with binary64 ends, and its mark: 0 when it has not been tested, 1 when the test leaves it undecided, and 2 when the test shows that every point of it fits.  The test of a box encloses `P` over the box with the frames demo's `cartesianI`, and for each measurement it encloses the residual `mₖ(x) − yₖ` over the box and the admissible parameters.  With the residual's interval `[e_lo, e_hi]`, a measurement excludes the box when the interval is accepted and `e_lo > εₖ` or `e_hi < −εₖ`, and it holds over the box when the interval is accepted and `−εₖ ≤ e_lo` and `e_hi ≤ εₖ`.  The test returns 0 when some measurement excludes the box, 2 when every measurement holds over it, and 1 otherwise.  A rejected interval excludes nothing and holds nothing, so a rejection only keeps a box.

The size of a box is the largest of `a (φ_hi − φ_lo)`, `a c (λ_hi − λ_lo)`, and `h_hi − h_lo`, each computed in binary64 with `a = 6378.137`, where `c` is 1 when the box holds latitude 0 and otherwise the larger of `|cos φ_lo|` and `|cos φ_hi|` from the library's `cos`.  For latitudes in `[−π/2, π/2]` it is the largest `|cos φ|` of the box, so the size bounds the box's extent on the ground.  The longest side is the first side in the order latitude, longitude, height that attains the size.  Each of the `N` levels takes the boxes of marks 1 and 2 unchanged and tests every box of mark 0, in the order of the boxes.  It drops a box whose test gives 0 and keeps it with mark 2 when the test gives 2.  When the test gives 1, it splits the box at the computed middle `lo + (hi − lo) · 0.5` of its longest side into the lower half and then the upper half, both of mark 0, when the size exceeds `r` and the computed middle lies strictly between the side's ends, and otherwise keeps it with mark 1.  The search starts from the region as one box of mark 0.  When a level would leave more than `C` boxes, the search keeps the boxes of the previous level and stops with status 1, and the count of box tests includes the tests of that abandoned level.  When a level leaves no box of mark 0, the search stops with status 0.  When `N` levels leave a box of mark 0, the status is 2.  A final pass tests each remaining box of mark 0, drops those whose test gives 0, and labels each kept box 1 when its mark or its final test is 2 and 0 otherwise.  The output lists the kept boxes in the order of the search.

Every box is tested once in the levels that complete, the abandoned level tests at most `C` boxes, and the final pass tests only boxes of mark 0, so the number of box tests is at most `(N + 1) C`.  A level stores at most `2 C` new boxes of seven words before the test against the cap, and the output holds at most `4 + 7 C` values, 458,756 at `C = 65536`.  The module's memory is at most 65,535 pages of 64 KiB, the verified compiler's cap, and the call theorem states the allocation bound that the generated code proves.  Status 0 means that every box labeled 0 was tested, left undecided, and not split: its computed size is at most `r`, or the computed middle of its longest side does not lie strictly between the side's ends, as for a side whose ends are so large that the middle overflows.

## Theorems

Each theorem has a layer over the real numbers and a layer about the program, which rests on the first through the interval enclosures.  For an input `xs`, an admissible parameter is a choice of an Earth-fixed state for each receiver, arising from admissible inputs as the section on receiver states describes, and of a carrier frequency in `[f_lo, f_hi]`.

| Code | Layer | Statement |
|---|---|---|
| M1 | Model | For a receiver whose coordinates are differentiable at `t` with derivatives `u` and whose position `s(t)` differs from `x`, the derivative of the Euclidean distance from `s` to `x` at `t` is `(s(t) − x) · u / ρ(t)`. |
| M2 | Model | For a TEME trajectory `r` with derivative `v` at `t` and a sidereal angle with derivative `ω` at `t`, the derivative of each coordinate of `E(θ(t′)) r(t′)` at `t′ = t` is that coordinate of `E(θ(t)) (v + ω (r₂(t), −r₁(t), 0))`. |
| M3 | Model | The derivative of `θ(t) = gmst82(julian(d, t))` is `ω(t)`. |
| G1 | Program | For a valid input whose status is not 4, every triple `(φ, λ, h)` of the region whose position `P(φ, λ, h)` fits the measurements for some admissible parameter lies in a returned box. |
| G2 | Program | For a valid input, every point of a box labeled 1 fits the measurements for every admissible parameter. |
| G3 | Program | For a valid input, every returned box lies in the region, and there are at most `C` of them. |
| G4 | Program | For a valid input, the status is 0, 1, 2, or 4, and not 4 for `F = 0`.  At status 0 at most `N` levels are completed and every box labeled 0 is not split by the rule of the method, at status 1 fewer than `N` levels are completed, and at status 2 all `N`. |
| G5 | Program | Status 3 holds exactly for the inputs that break a requirement of the interface. |
| C1 | Compilation | The module's entry `locate`, called with the input array, returns the array of `locate` without a trap from a store with room for the generated allocation bound. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  G1 holds for unfinished searches at a coarser resolution, and an output that returns the region as one box labeled 0 satisfies G1 to G3.  The program's text, which C1 ties to the module, fixes the method, and the tests check that the output follows it.  G1 with an empty output states that no position of the region is consistent with the measurements.

## Tests

An oracle in Python with mpmath, written apart from the program, evaluates the model of this document with its own formulas: the WGS 84 position, the distances and range rates, and the two measurement models, in binary64 for dense sampling and in mpmath at 30 digits for every sample within `10⁻⁹` of a bound.  For `F = 1` it computes the sidereal angle from the GMST 1982 polynomial in the Julian date, rotates with its own matrices, and takes the Earth-fixed velocity as the numerical derivative of the rotated position along the receiver's straight-line motion.  Each case places an emitter, receivers around the Earth, and measurements drawn within 0.8 of their bounds of the model's values for a random admissible parameter.

For each case the oracle takes seven parameters: the center of every interval, the parameter that produced the measurements, three random parameters, and two random corners, each component at one end of its interval.  For each parameter it covers the region by a Lipschitz subdivision: a cell is dropped when some residual at its center exceeds the bound by more than a bound of the residual's change over the cell, from `|∂P/∂φ| ≤ 6400 + h`, `|∂P/∂λ| ≤ (6400 + h) |cos φ|`, and the gradients `2/c` and `f₀/c · (2|uᵢ|/ρᵢ + 2|uⱼ|/ρⱼ)`, and the remaining cells are split until their size is at most `r`, or 0.02 km and 0.2 km for `wide-receiver-intervals` and `teme-wide-time`.  It samples 4 points along each side of every remaining cell, at fractions 0.1, 0.35, 0.6, and 0.85 that no bisection reaches, and a sample is consistent for the parameter when every residual lies within its bound.

The test requires:

- status 3 and the output `3, 0, 0, 0` exactly for the invalid inputs, and `4, 0, 0, 0` for the case of status 4;
- for valid inputs, the status that each case states, `4 + 7 K` values, labels 0 and 1, at most `C` boxes, at most `(N + 1) C` box tests, `N` levels completed at status 2, fewer than `N` at status 1, at most `N` at status 0, and boxes with ordered ends inside the region;
- the number of boxes, the presence of boxes labeled 1, and boxes at both ends of the longitude, where the case states them;
- every consistent sample of every parameter to lie in a returned box;
- every corner, the center, and six random points of each box labeled 1 to fit the measurements for every parameter;
- at status 0, every box labeled 0 to have a binary64 size at most `r` or no computed middle strictly inside its longest side, and no two boxes to overlap in more than their boundaries.

The test also checks that the output follows the method: at every status, the center of every returned box must fit each measurement for the central parameter within `εₖ` plus eight times the sum of bounds of the measurement's change over the box and over the admissible parameters, the second from the largest moves of each receiver's Earth-fixed position and velocity over its intervals and the half-width of the frequency's interval.  A mutation run alters correct outputs so that each alteration is wrong: it removes the box that holds the most consistent samples, moves an end of a box past a consistent sample that no other box holds, labels 1 a box with a corner that fails for the central parameter, reports status 3, and returns the region as one box labeled 1.  The test must fail on each.

| Case | `F` | Receivers | Kinds and `ε` | `r` (km) | `N`, `C` | Region and other inputs | Expected |
|---|---|---|---|---|---|---|---|
| `meo4-tdoa` | 0 | Four at 23,222 km altitude | Time, 1 μs | 0.2 | 60, 65536 | ±2° about the emitter at 35°, 40° on the ellipsoid | Status 0 |
| `meo4-fdoa` | 0 | The same | Frequency, 0.5 Hz | 0.2 | 60, 65536 | The same | Status 0 |
| `meo4-both` | 0 | The same | Both | 0.2 | 60, 65536 | The same | Status 0 |
| `leo2-two-solutions` | 0 | Two at 800 km in one orbit, 2.5° apart | Time 0.2 μs, frequency 1 Hz | 0.2 | 60, 65536 | ±10° | Status 0 |
| `aircraft` | 0 | Four at 23,222 km | Both | 0.25 | 60, 65536 | ±1°, heights 0 to 12 km, emitter at 9 km | Status 0 |
| `vertical-line` | 0 | The same | Both | 0.01 | 60, 65536 | One latitude and longitude, heights 0 to 12 km | Status 0 |
| `receiver-intervals` | 0 | The same, ±0.01 km and ±10⁻⁵ km/s | Both | 0.2 | 60, 65536 | ±2° | Status 0 |
| `wide-receiver-intervals` | 0 | The same, ±0.5 km and ±10⁻⁴ km/s | Time, 0.1 μs | 0.02 | 60, 65536 | ±2° | Status 0 |
| `f-wide-fine` | 0 | Three at 800 km | Frequency, 0.1 Hz | 0.02 | 60, 65536 | ±0.5° | Status 0 |
| `whole-earth` | 0 | Four at 23,222 km | Both | 1 | 60, 65536 | The whole Earth | Status 0 |
| `region-without-emitter` | 0 | The same | Both | 0.2 | 60, 65536 | ±1° about 11°, 11° | Status 0, no box |
| `inconsistent` | 0 | The same | Both, the first time difference moved by 50 μs | 0.2 | 60, 65536 | ±2° | Status 0, no box |
| `near-pole` | 0 | Four at 23,222 km | Both | 0.2 | 60, 65536 | Latitudes 88° to `π/2⁺`, longitudes 0 to 2π, emitter at 89.9° | Status 0 |
| `at-pole` | 0 | The same | Both | 0.2 | 60, 65536 | Latitudes 89° to `π/2⁺`, longitudes `−π⁻` to `π⁺`, emitter at 89.998° | Status 0 |
| `antimeridian` | 0 | Four at 23,222 km | Both | 0.2 | 60, 65536 | Longitudes 3.0 to 3.3 rad, emitter at 179.9999° | Status 0 |
| `antimeridian-ends` | 0 | The same | Both | 0.2 | 60, 65536 | Longitudes `−π⁻` to `π⁺` | Status 0, boxes at both ends |
| `ground-receiver` | 0 | One at rest on the ellipsoid 25 m from the emitter, three at 23,222 km | Both | 0.01 | 60, 65536 | ±0.05° | Status 0 |
| `levels-zero` | 0 | Four at 23,222 km | Both | 0.2 | 0, 65536 | ±2° | Status 2, one box |
| `levels-zero-far` | 0 | The same | Both | 0.2 | 0, 65536 | ±1° about 20°, 60° | Status 2, no box |
| `label-one-final` | 0 | The same | Time, 1 ms | 5 | 0, 65536 | ±0.1° | Status 2, one box labeled 1 |
| `label-one-levels` | 0 | The same | Time, 20 μs | 0.5 | 60, 65536 | ±2° | Status 0, boxes labeled 1 |
| `levels-ten` | 0 | The same | Both | 0.2 | 10, 65536 | ±2° | Status 2 |
| `levels-exact` | 0 | The same as `meo4-both` | Both | 0.2 | the levels of `meo4-both`, 65536 | ±2° | Status 0 |
| `cap-four` | 0 | Four at 23,222 km | Both | 0.2 | 60, 4 | ±2° | Status 1 |
| `cap-one` | 0 | The same | Both | 0.2 | 60, 1 | ±2° | Status 1 |
| `wide-bounds` | 0 | The same | Time 20 μs, frequency 5 Hz | 0.5 | 60, 65536 | ±2° | Status 0 |
| `teme-both` | 1 | Four at 23,222 km, times ±1 μs | Both | 0.2 | 60, 65536 | Polar motion 0.1″ and 0.3″ ± 0.01″ | Status 0 |
| `teme-tdoa` | 1 | The same | Time, 1 μs | 0.2 | 60, 65536 | Polar motion 0.1″ and 0.3″ | Status 0 |
| `teme-fdoa` | 1 | The same | Frequency, 0.2 Hz | 0.2 | 60, 65536 | The same | Status 0 |
| `teme-fdoa-leo` | 1 | Three at 800 km | Frequency, 0.1 Hz | 0.02 | 60, 65536 | ±0.5° | Status 0 |
| `teme-wide-time` | 1 | Four at 23,222 km, times ±5 s | Both | 2 | 60, 65536 | ±2° | Status 0 |
| `teme-big-polar` | 1 | The same | Both | 0.5 | 60, 65536 | Polar motion 20,000″ and 30,000″, ±6° | Status 0 |
| `teme-status-four` | 1 | The same, the first receiver's time at `10³⁰⁰` s | Both | 0.2 | 60, 65536 | ±2° | Status 4 |

The invalid inputs break each requirement of the interface once: the version, the frame, the counts, the day, the order of every kind of interval, the frequency, the resolution, the levels, the cap, the kind, each receiver index including `−1` and `n`, equal indices, a negative bound, a NaN, an infinity, and lengths one short, one long, and empty.  The tests measure the box tests and the time of a call in the WebAssembly module.  A module test compares the WebAssembly module with native Lean bit for bit, which fixes the order of the output boxes that the method states.

## What lies outside the theorems

The theorems concern the stated model: an emitter fixed on the rotating Earth, instantaneous distances, the first-order Doppler shift, receivers in the intervals the caller gives, and for `F = 1` the frames demo's GMST 1982 and polar-motion rotation.  The light time, the atmosphere, the relativistic terms, the emitter's motion, the conversion of the measurements to the receivers, and the receivers' intervals are the caller's premises.  The theorems bound no width and no count: a coarse result is sound, and the number and sizes of the boxes depend on `r`, `N`, `C`, and the rounding.  No theorem states that the boxes do not overlap, which the tests check, and a box labeled 0 may hold no consistent position, since the interval evaluation over a box overestimates the range of a residual.

## References

- Cospas-Sarsat, [Introduction to the Cospas-Sarsat system](https://www.cospas-sarsat.int/en/system/overview), C/S G.003, and the specification of 406 MHz beacons, C/S T.001.
- European Space Agency, [Galileo facts and figures](https://www.esa.int/Applications/Satellite_navigation/Galileo/Facts_and_figures).
- D. A. Vallado, P. Crawford, R. Hujsak, and T. S. Kelso, [Revisiting Spacetrack Report #3](https://celestrak.org/publications/AIAA/2006-6753/), AIAA 2006-6753.
- G. Petit and B. Luzum (eds.), [IERS Conventions (2010)](https://www.iers.org/iers/en/publications/technicalnotes/tn36), IERS Technical Note 36.
- National Geospatial-Intelligence Agency, [World Geodetic System 1984](https://earth-info.nga.mil/index.php?dir=wgs84&action=wgs84), NGA.STND.0036.
- R. Krawczyk, Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken, Computing 4, 1969, 187–201.
- [The frames and time demo](../Frames/README.md)
- [The interval library](../../Library/Numerics/Interval/README.md)
