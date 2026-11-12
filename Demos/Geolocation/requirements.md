# Emitter geolocation requirements

## Purpose and scope

The program locates a radio emitter from time differences and frequency differences of arrival at several receivers, with bounded measurement errors.  It returns boxes of geodetic coordinates that contain every emitter position consistent with the measurements, within the stated error bounds, and for receiver states anywhere in their stated boxes.  The search is an interval branch-and-prune: a box is discarded only when interval evaluation shows that no point of it fits the measurements.  A second label marks the boxes in which every point fits, so the result also certifies positions that the measurements cannot exclude.

Its uses are the location of distress beacons, as the medium-altitude system of Cospas-Sarsat (MEOSAR) does with these two measurement types, and the location of sources of radio interference.  The program is a ground program compiled to WebAssembly by the verified compiler, in its dialect of `UInt64` and binary64 values with bounded loops.  Receiver states and their error bounds come from the caller: from an ephemeris in the Earth-fixed frame, or in the TEME frame of SGP4 at the time of each receiver, which the program rotates into the Earth-fixed frame with the sidereal time and polar motion of [the frames and time demo](../Frames/README.md).

The theorems concern a stated measurement model.  Light time, the rotation of the Earth during the light time, atmospheric delays, relativistic terms, and the conversion of the measurements from a ground station to the receivers lie outside it, and [the section on the model's limits](#what-the-model-leaves-out) gives their sizes so that the caller can add them to the error bounds.  Existence or uniqueness of a solution within a box, by a Krawczyk test, is left for a later iteration.

## The emitter

The emitter is fixed on the rotating Earth at the position with geodetic latitude `φ`, longitude `λ`, and height `h` on the WGS 84 ellipsoid, `x = P(φ, λ, h)`, where `P` is `Demos.Frames.Model.position` of the frames demo:

`P(φ, λ, h) = ((N + h) cos φ cos λ, (N + h) cos φ sin λ, (N (1 − e²) + h) sin φ)`,  `N = a / √(1 − e² sin² φ)`,

with `a = 6378.137` km and `e² = f (2 − f)` for `f = 1/298.257223563`.  The caller gives a search region `[φ₀, φ₁] × [λ₀, λ₁] × [h₀, h₁]` of coordinates in radians and km.  An emitter on the ellipsoid has `h₀ = h₁ = 0`, an emitter on land a range of terrain heights such as `[−0.5, 9]` km, and an emitter on an aircraft a range up to its ceiling.  The region `[−1.5707963267948968, 1.5707963267948968] × [−3.1415926535897936, 3.1415926535897936] × [h₀, h₁]`, whose bounds are the binary64 values just beyond `±π/2` and `±π`, holds geodetic coordinates of every point whose geodetic height lies in `[h₀, h₁]`.  The theorems state their results for coordinate triples of the region, and by `P` for the Earth-fixed points of those triples.

## Measurement model

A receiver `i` has the Earth-fixed position `sᵢ` in km and velocity `uᵢ` in km/s, the velocity relative to the rotating Earth.  With `ρᵢ(x) = |sᵢ − x|`, the Euclidean distance, and the speed of light `c = 299792.458` km/s, the model of each measurement is

| Measurement | Model at the emitter position `x` | Unit |
|---|---|---|
| Time difference of arrival `τᵢⱼ`, the arrival time at `i` less that at `j` | `(ρᵢ(x) − ρⱼ(x)) / c` | s |
| Frequency difference of arrival `νᵢⱼ`, the received frequency at `i` less that at `j` | `−f (ρ̇ᵢ(x) − ρ̇ⱼ(x)) / c` | Hz |

with the range rate `ρ̇ᵢ(x) = (sᵢ − x) · uᵢ / ρᵢ(x)` and the emitted carrier frequency `f` in Hz.  The range rate is the time derivative of `ρᵢ` along the receiver's motion for an emitter fixed in the Earth-fixed frame (theorem M1), so the frequency model is the first-order Doppler shift `f (1 − ρ̇ᵢ/c)` received at `i`, less that at `j`.  The carrier frequency is unknown within an interval `[f_lo, f_hi]` that the caller gives: the 406 MHz beacons of Cospas-Sarsat transmit in the band from 406.0 to 406.1 MHz, and an uncertainty of `2.5·10⁻⁴` in `f` changes a frequency difference of 10 kHz by 2.5 Hz.

A measurement `k` names two distinct receivers `i` and `j`, a measured value `yₖ`, and a bound `εₖ ≥ 0`.  An emitter position `x` fits the measurements for receiver states `(sᵢ, uᵢ)` and a carrier frequency `f` when `|mₖ(x) − yₖ| ≤ εₖ` for every measurement `k`, where `mₖ` is the model of the measurement's kind.  The position is consistent with the measurements when it fits them for some admissible receiver states and some `f` in `[f_lo, f_hi]`.

## Receiver states

The caller gives each receiver's state as six intervals, one per component of its position and velocity, and the admissible states are those whose components lie in the intervals.  An exact state is an interval of zero width.  The frame `F` of the input fixes how the intervals give the Earth-fixed states.

**Earth-fixed input (`F = 0`).**  The intervals hold the components of `sᵢ` and `uᵢ` in the Earth-fixed frame, as GNSS broadcast ephemerides give them: WGS 84 or the ITRF, with the velocity relative to the rotating Earth.

**TEME input (`F = 1`).**  The intervals hold the components of the position `rᵢ` and velocity `vᵢ` in the TEME frame of SGP4, and a further interval holds the time `tᵢ` of the state in seconds of UT1 from the start of the day `d`, a Modified Julian Date.  Intervals `xp` and `yp` of polar motion in arcseconds hold for all receivers.  With the rotation `E(θ) = R1(−yp) R2(−xp) R3(θ)` and the sidereal angle `θ(t) = gmst82(JD(d, t))` of `Demos.Frames.Model`, the Earth-fixed state is

`sᵢ = E(θ(tᵢ)) rᵢ`,  `uᵢ = E(θ(tᵢ)) (vᵢ + ω(tᵢ) (rᵢ,₂, −rᵢ,₁, 0))`,

where `ω(t)` is the derivative of `θ` with respect to `t`,

`ω(t) = (π/43200) (1 + (8640184.812866 + T (0.186208 − 1.86·10⁻⁵ T)) / 3155760000)`,  `T = (d − 51544.5 + t/86400) / 36525`,

about `7.2921158·10⁻⁵` rad/s.  The term in `ω` is `−ω ẑ × r` in the frame of `R3(θ)`, and theorem M2 states that `uᵢ` is the derivative of `E(θ(t)) r(t)` at `tᵢ` for a TEME trajectory `r` with `r(tᵢ) = rᵢ` and `r′(tᵢ) = vᵢ`, with polar motion constant over the time.  This is the transformation of the function `teme2ecef` of Vallado's SGP4 code, with the order of the polar-motion rotations of the frames demo and `ω` derived from GMST 1982, which differs from that code's constant `7.29211514670698·10⁻⁵` rad/s by `7·10⁻¹²` rad/s, or `2·10⁻⁷` km/s at 29,600 km.  The rate is per second of UT1, which differs from the SI second by the excess length of day, about `10⁻⁸` relative.  An admissible state of a receiver has `tᵢ`, `rᵢ`, and `vᵢ` in their intervals, and `xp` and `yp`, one value for all receivers, in theirs.

## What the model leaves out

The model takes each receiver's state at the time of arrival at that receiver and the emitter fixed in the Earth-fixed frame, and it uses the instantaneous distance.  The signal travels in an inertial frame, and during the light time `L/c` the Earth turns by `ω L/c`, which moves the emitter by at most `ω L p / c` for its distance `p` from the polar axis and changes the path length by no more.  For `p ≤ 6378` km this is 45 m, or 0.15 μs, at a range of 28,900 km, the largest range from a Galileo satellite to the Earth's surface, and 4.7 m at 3,000 km.  A time difference therefore differs from the model by up to twice the larger of the two receivers' amounts, and the caller adds this to `εₖ`.  The ionosphere delays a signal by `40.3 · TEC / f²` m for a total electron content `TEC` in electrons per m², about 122 m, or 0.41 μs, at 406 MHz for 50 TEC units along the path, and the troposphere by about 2.4 m at the zenith and more at low elevation.  Only the difference between the two paths enters a time difference.

The frequency model is the first-order Doppler shift.  Terms of second order in `v/c`, for a receiver speed `v` relative to an inertial frame, amount to about `f (v/c)²`: 0.07 Hz at 406 MHz for 3.9 km/s, the speed of a MEOSAR satellite, and 0.25 Hz for 7.5 km/s in a low orbit.  The difference of gravitational potential between the emitter and a receiver shifts the frequency by up to about 0.22 Hz at 406 MHz for a receiver at 29,600 km from the Earth's center, and it cancels in a difference between receivers at equal distances.  Drift of the emitter's carrier during the measurements, the receivers' clock and frequency errors, and the conversion of times and frequencies measured at a ground station through a transponder to the receivers are the caller's, and each enters `εₖ`, `[f_lo, f_hi]`, or the receivers' intervals.

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
| `20 + 14 n + 5 k` to `24 + 14 n + 5 k` | Measurement `k`: its kind, 1 for a time difference and 2 for a frequency difference, the receivers `i` and `j`, the value `yₖ` (s or Hz), and the bound `εₖ` | Kind 1 or 2, `i` and `j` whole, below `n`, and distinct, `εₖ ≥ 0` |

The entries that the frame does not use, the day and polar motion for `F = 0` and the receivers' times for `F = 0`, must still meet their requirements.  An input that breaks a requirement gives the output `3, 0, 0, 0`.

| Output index | Value |
|---|---|
| 0 | Status: 0 complete, 1 stopped at the cap, 2 stopped after `N` levels, 3 invalid input, 4 receiver states that the interval arithmetic rejects |
| 1 | Number `K` of boxes |
| 2 | Number of box tests |
| 3 | Number of levels completed |
| `4 + 7 j` to `10 + 7 j` | Box `j`: `φ` from, `φ` to, `λ` from, `λ` to, `h` from, `h` to, and its label, 1 when every point of the box fits the measurements for every admissible state and frequency, and 0 otherwise |

Status 4 occurs when an interval of a receiver's Earth-fixed state is rejected, as on overflow, and its output is `4, 0, 0, 0`.  For `F = 0` the input's intervals are the states, so status 4 does not occur.

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding.  The model takes the real values of the binary64 inputs, and each decimal constant, such as `c`, enters as the interval of an exact ratio of integers.  It first encloses the Earth-fixed state of each receiver: for `F = 0` the input's intervals, and for `F = 1` the rotation of the frames demo's `angleWith` and `toEarthI` applied to the TEME intervals at the interval of `tᵢ`, and to the velocity term with an enclosure of `ω(tᵢ)`.  It encloses the carrier frequency by `[f_lo, f_hi]`.  An interval operation rejects on overflow, on a divisor that the arithmetic cannot show nonzero, and on a square-root operand whose lower end is negative.

A box is a triple of intervals of latitude, longitude, and height with binary64 ends, and its mark: 0 when it has not been tested, 1 when the test leaves it undecided, and 2 when the test shows that every point of it fits.  The test of a box encloses `P` over the box with the frames demo's `cartesianI`, and for each measurement it encloses the residual `mₖ(x) − yₖ` over the box and the admissible states and frequencies.  With the residual's interval `[e_lo, e_hi]`, a measurement excludes the box when the interval is accepted and `e_lo > εₖ` or `e_hi < −εₖ`, and it holds over the box when the interval is accepted and `−εₖ ≤ e_lo` and `e_hi ≤ εₖ`.  The test returns 0 when some measurement excludes the box, 2 when every measurement holds over it, and 1 otherwise.  A rejected interval excludes nothing and holds nothing, so a rejection only keeps a box.

The size of a box is the largest of `a (φ_hi − φ_lo)`, `a (λ_hi − λ_lo)`, and `h_hi − h_lo`, each computed in binary64 with `a = 6378.137`, and its longest side is the first side in the order latitude, longitude, height that attains the size.  Each of the `N` levels takes the boxes of marks 1 and 2 unchanged and tests every box of mark 0.  It drops a box whose test gives 0, keeps it with mark 2 when the test gives 2, and when the test gives 1 it splits the box in two at the computed middle `lo + (hi − lo) · 0.5` of its longest side, as two boxes of mark 0, when the size exceeds `r` and the middle lies strictly between the side's ends, and otherwise keeps it with mark 1.  The search starts from the region as one box of mark 0.  When a level would leave more than `C` boxes, the search keeps the boxes of the previous level and stops with status 1.  When a level leaves no box of mark 0, the search stops with status 0.  When `N` levels leave a box of mark 0, the status is 2.  A final pass tests each remaining box of mark 0, drops those whose test gives 0, and labels each kept box 1 when its mark or its final test is 2 and 0 otherwise.  The boxes appear in the output in the order of the search.

Every box is tested at most once in the levels, and once more in the final pass only when it has mark 0, so the number of box tests is at most `(N + 1) C`.  A level stores at most `2 C` new boxes of seven words before the test against the cap.  Status 0 means that every box labeled 0 was tested, left undecided, and not split: its size is at most `r`, or its longest side has no binary64 middle strictly between its ends.

## Theorems

Each theorem has a layer over the real numbers and a layer about the program, which rests on the first through the interval enclosures.  For an input `xs`, an admissible parameter is a choice of an Earth-fixed state for each receiver, arising from admissible inputs as the section on receiver states describes, and of a carrier frequency in `[f_lo, f_hi]`.

| Code | Layer | Statement |
|---|---|---|
| M1 | Model | For a receiver trajectory `s` differentiable at `t` with `s′(t) = u` and `s(t) ≠ x`, the derivative of `|s − x|` at `t` is `(s(t) − x) · u / |s(t) − x|`. |
| M2 | Model | For a TEME trajectory `r` with derivative `v` at `t`, the derivative of `E(θ(t′)) r(t′)` at `t′ = t` is `E(θ(t)) (v + ω(t) (r₂(t), −r₁(t), 0))`. |
| M3 | Model | The derivative of `θ(t) = gmst82(JD(d, t))` is `ω(t)`. |
| G1 | Program | For a valid input with status 0, 1, or 2, every triple `(φ, λ, h)` of the region whose position `P(φ, λ, h)` fits the measurements for some admissible parameter lies in a returned box. |
| G2 | Program | For a valid input, every point of a box labeled 1 fits the measurements for every admissible parameter. |
| G3 | Program | For a valid input, every returned box lies in the region, and there are at most `C` of them. |
| G4 | Program | For a valid input, the status is 0, 1, 2, or 4, output 3 is the number of levels completed, status 0 comes with every box labeled 0 left undecided and not split, status 1 with a next level of more than `C` boxes, and status 2 with all `N` levels completed. |
| G5 | Program | Status 3 holds exactly for the inputs that break a requirement of the interface. |
| C1 | Compilation | The module's entry `locate`, called with the input array, returns the array of `locate` without a trap from a store with room for the generated allocation bound. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  G1 holds for unfinished searches at a coarser resolution, and an output that returns the region as one box labeled 0 satisfies G1 to G3.  The program's text, which C1 ties to the module, fixes the method, and the tests check that the output follows it.  G1 with an empty output states that no position of the region is consistent with the measurements.

## Tests

An oracle in Python with mpmath, written apart from the program, evaluates the model of this document at 30 digits: the WGS 84 position, the distances and range rates, the two measurement models, and for `F = 1` the sidereal angle, its rate, and the rotation, with its own matrices.  Each case places an emitter, receivers on orbits around the Earth, and measurements drawn within their bounds of the model's values for some admissible parameter.  To sample consistent positions densely, the oracle finds every solution of the measurement equations in the region by a multistart Newton iteration in mpmath, for the central parameter and for random admissible parameters, and samples a grid around each solution out to where the residuals exceed their bounds.  A sample is consistent for a parameter when each residual lies within its bound.

The test requires:

- status 3 and the output `3, 0, 0, 0` exactly for the invalid inputs;
- for valid inputs, the status that each case states, `4 + 7 K` values, labels 0 and 1, at most `C` boxes, at most `(N + 1) C` box tests, `N` levels completed at status 2, fewer than `N` at status 1, and boxes with ordered ends inside the region;
- every consistent sample, both for the central parameter and for each random parameter, to lie in a returned box;
- every sample of a box labeled 1 to fit the measurements for the central parameter, for random parameters, and for the corners of the parameter's intervals;
- at status 0, every box labeled 0 to have a binary64 size at most `r` or no middle strictly inside its longest side, and no two boxes to overlap in more than their boundaries.

The test also checks that the output follows the method where the enclosures are tight: at status 0, the center of every returned box must fit each measurement for the central parameter within `εₖ` plus a bound of the measurement's change over the box and the parameter's intervals.  A mutation run alters correct outputs so that each alteration is wrong: it removes the box that holds the most consistent samples, moves an end of a box past a consistent sample, labels 1 a box that holds a sample that fits no admissible parameter, reports status 3, and returns the region as one box labeled 1.  The test must fail on each.

The cases include an emitter on the ellipsoid with four MEOSAR-like receivers and time differences only, the same with frequency differences only and with both, two low-orbit receivers with one time and one frequency difference, which leave two solutions, an emitter on an aircraft with a range of heights, receiver states with nonzero intervals, the TEME frame with a time and polar motion, the whole Earth as region, a region that excludes the emitter, measurements that no position fits, an emitter near a pole and one near the antimeridian, `N = 0`, a small cap, and invalid inputs.  The tests measure the box tests and the time of a call in the WebAssembly module.  A module test compares the WebAssembly module with native Lean bit for bit.

## What lies outside the theorems

The theorems concern the stated model: an emitter fixed on the rotating Earth, instantaneous distances, the first-order Doppler shift, receivers in the intervals the caller gives, and for `F = 1` the frames demo's GMST 1982 and polar-motion rotation.  The light time, the atmosphere, the relativistic terms, the conversion of the measurements to the receivers, and the receivers' intervals are the caller's premises.  The theorems bound no width and no count: a coarse result is sound, and the number and sizes of the boxes depend on `r`, `N`, `C`, and the rounding.  No theorem states that the boxes do not overlap or that a box labeled 0 holds a consistent position, which the tests check.

## References

- Cospas-Sarsat, [Introduction to the Cospas-Sarsat system](https://www.cospas-sarsat.int/en/system/overview), C/S G.003, and the specification of 406 MHz beacons, C/S T.001.
- D. A. Vallado, P. Crawford, R. Hujsak, and T. S. Kelso, [Revisiting Spacetrack Report #3](https://celestrak.org/publications/AIAA/2006-6753/), AIAA 2006-6753.
- G. Petit and B. Luzum (eds.), [IERS Conventions (2010)](https://www.iers.org/iers/en/publications/technicalnotes/tn36), IERS Technical Note 36.
- National Geospatial-Intelligence Agency, [World Geodetic System 1984](https://earth-info.nga.mil/index.php?dir=wgs84&action=wgs84), NGA.STND.0036.
- R. Krawczyk, Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken, Computing 4, 1969, 187–201.
- [The frames and time demo](../Frames/README.md)
- [The interval library](../../Library/Numerics/Interval/README.md)
