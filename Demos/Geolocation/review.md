# Emitter geolocation requirements: decisions and review

[The requirements](requirements.md) specify candidate 6.4 of the space-operations plan, from brief 6.4 of the candidates' briefs.  This record gives each decision with its reason, the findings of the independent review, and the response to each.

## Decisions

| Question | Choice | Reason |
|---|---|---|
| Emitter constraint | The emitter lies in a box of geodetic coordinates whose height range the caller gives | One input covers an emitter on the ellipsoid (`h₀ = h₁ = 0`), on land, and on an aircraft.  The frames demo's `cartesianI` and `cartesian_eq` give the enclosure of the position and its model, and a search over Cartesian boxes would spend boxes away from the Earth. |
| Receiver errors | An interval for every component of each receiver's position and velocity, and for TEME its time | Interval inputs cost the program nothing, and the theorems then hold for every state in the intervals.  An exact state is an interval of zero width. |
| Frame of the receivers | Earth-fixed, or TEME at each receiver's time of UT1 with polar motion | GNSS broadcast ephemerides, as MEOSAR uses, give Earth-fixed states, and SGP4 gives TEME states, which the frames demo's sidereal time and rotation carry into the Earth-fixed frame. |
| Measurement model | Instantaneous distances and the first-order Doppler shift in the Earth-fixed frame | The theorems concern a model that the program evaluates exactly in interval arithmetic.  The requirements bound the light time, the atmosphere, the second-order and gravitational terms, and the emitter's motion for the caller's error bounds. |
| Carrier frequency | An interval | A 406 MHz beacon's frequency is known to about `2.5·10⁻⁴`, which changes a frequency difference of 10 kHz by 2.5 Hz. |
| Search | Level by level: each level tests every untested box and drops, marks, or splits it, and tested boxes keep their marks | A level's boxes have one resolution, so an unfinished search returns a uniform cover, and the screening demo's `loop_cover` and `loop_size_le` carry the proofs.  Each box is tested once in the levels. |
| Size of a box | `a` times the latitude's extent, `a` times the largest `|cos φ|` times the longitude's extent, and the height's extent | The resolution then bounds the extent on the ground.  With `a` times the longitude's extent alone, the search near a pole split boxes in longitude far below the resolution: the first module stopped at the cap with 34,204 boxes for an emitter at 89.9°, and the review's model stopped at 43,254 boxes at 89.99°. |
| Label | 1 when every point of a box fits every admissible parameter | The same enclosures give it, and it certifies positions that the measurements cannot exclude. |
| Statuses | 0 complete, 1 stopped at the cap, 2 stopped after `N` levels, 3 invalid, 4 receiver intervals rejected | G1 holds at statuses 0, 1, and 2, and status 0 is the accepting status. |
| Krawczyk test | Left for a later iteration | The request makes it optional and later than the soundness theorem. |
| Target | A ground program: a WebAssembly module of the verified compiler | A MEOSAR ground station computes the locations. |

## Review

A fresh agent reviewed the requirements against brief 6.4, the plan's sections "Starting point" and "What every design states" and its correction for 6.4, and the added scope, with [the method of independent review](../../VKB/entries/independent-review/README.md).  It received none of the author's reasoning.  It built its own model of the program in numpy, with each operation rounded to nearest and moved one step outward, the frames demo's enclosures in their groupings, and the branch-and-prune with its marks, levels, cap, statuses, final pass, and output layout.  Its oracle in mpmath used formulations that differ from the requirements': the WGS 84 position from the reduced latitude and the surface normal, the Doppler shift from a central difference of the range along the receiver's line, the TEME-to-Earth-fixed velocity from the derivative of the rotated trajectory, and the consistent set from a Lipschitz subdivision of the region for each sampled parameter.

Over 14 listed cases, 16 added cases, 160 random inputs, and 3 further cases, about 458 million consistent samples in all, the model had no cover failure and no failure of a box labeled 1.  The reviewer confirmed the region's bounds, the WGS 84 position against ERFA's `gd2gc` to `1.8·10⁻¹²` km, the formula and the value `7.29211585542·10⁻⁵` rad/s of `ω` against the derivative of GMST 1982, the sign of the rotation term and its agreement with Vallado's `v_pef = R3 v − ω × r_pef`, the order of the polar-motion rotations against ERFA's `pom00`, and the light-time bound by an inertial simulation of 55 pairs of receivers, whose largest error was 0.82 of the stated bound.  M2 matched a numerical derivative to `7·10⁻³⁴` km/s and M3 to `1.4·10⁻⁴³`.

| Finding | Severity | Response |
|---|---|---|
| 1. The method check rejects a correct program: with a rigorous bound of the change over a box and the largest change over sampled parameters, correct outputs exceed it by up to 2.56 times on random inputs and 12.6 times with a 10 s time interval, since interval evaluation keeps boxes that a Lipschitz bound excludes. | Defect | Adopted.  The check allows eight times the sum of bounds of the change over the box and over every admissible parameter, the second from the largest moves of the receivers' states over their intervals and the frequency's half-width, and every correct output of the cases meets it. |
| 2. The method check runs only at status 0, where the final pass changes nothing, so a program without the final pass, or one that labels but drops nothing, passes every case. | Gap | Adopted.  The check runs at every status, and `levels-zero-far` states no box and `label-one-final` one box labeled 1, both at status 2. |
| 3. The cover test samples the central and random parameters, whose consistent sets are empty when the intervals are wide relative to `ε`, so a program that collapses the intervals to their centers passes. | Gap | Adopted.  The parameter that produced the measurements is one of the oracle's seven, the subdivision runs for each parameter, and `wide-receiver-intervals` and `teme-wide-time` have intervals wide relative to `ε`. |
| 4. The listed cases do not state their kinds, bounds, resolutions, levels, caps, widths, or statuses, and what they reject depends on those choices: no listed case returned a box labeled 1, `f₀` taken at `f_lo` was rejected by 11 samples of 26,721, and no case reached a rejected interval except by geometry. | Gap | Adopted.  The requirements give a table of the cases with each value and expectation, among them `f-wide-fine` with three low-orbit receivers at 0.1 Hz, `label-one-final` and `label-one-levels` with boxes labeled 1 from the final pass and from the levels, and `ground-receiver` with a receiver inside the region, where the division rejects. |
| 5. No case reaches status 4, so a program that reports 3 there, or ignores the rejection, passes. | Gap | Adopted.  `teme-status-four` puts a receiver's time at `10³⁰⁰` s, and the module test has the same input. |
| 6. A program that never labels 1, or ignores a final test of 2, passes. | Gap | Adopted with `label-one-final` and `label-one-levels`. |
| 7. The pole and antimeridian cases reach neither the pole nor both ends of the longitude, and with the size `a Δλ` an emitter at the pole stops the search at the cap. | Gap | Adopted.  The size uses the largest `|cos φ|` of a box, as the decisions record, `at-pole` reaches the pole, and `antimeridian-ends` requires boxes at both ends of the longitude. |
| 8. Some wrong programs need valid but unrealistic inputs: polar motion swapped or omitted moves a position by 0.17 mm at 0.5″, the height taken at its lower end needs a region without horizontal extent, status 2 at exactly `N` levels needs that `N`, and no case reaches the cap at the first level. | Gap | Adopted with `teme-big-polar` at 20,000″ and 30,000″, `vertical-line`, `levels-exact`, and `cap-one`. |
| 9. The sentence that status 0 means a size at most `r` or no middle strictly inside is false for heights of `±10³⁰⁸`, where the computed middle overflows while binary64 values lie inside. | Defect | Adopted.  The method speaks of the computed middle, as G4 and the program's `splits` do. |
| 10. The sentence that the tests check that a box labeled 0 holds a consistent position is false: correct outputs have boxes labeled 0 without one, 71 of 193 in one case. | Defect | Adopted.  The requirements state that a box labeled 0 may hold no consistent position. |
| 11. A moving emitter lies outside the model, and the section on the model's limits omits it: an aircraft at 0.25 km/s moves a frequency difference by up to 677 Hz. | Gap | Adopted.  The section gives `f₀ w / c` for each frequency and twice that for a difference. |
| 12. The requirements state no memory cap or cost bound. | Gap | Adopted.  The method gives the bounds on tests, stored boxes, the output, and the module's memory, and the README the measured costs. |
| 13. "Finds every solution by a multistart Newton iteration" guarantees no component when there are more measurements than unknowns. | Wording | Adopted.  The oracle covers the region by a Lipschitz subdivision for each parameter. |
| 14. "The corners of the parameter's intervals" are too many to test: four receivers give `2²⁵`. | Wording | Adopted.  The oracle takes two random corners. |
| 15. "In the order of the search" fixes neither the position of kept boxes nor the order of the halves, and the count of tests at the cap is unstated. | Wording | Adopted.  The method states both orders and that the count includes the abandoned level.  No theorem states the order, and the module test against native Lean fixes it. |
| 16. "Whole, below `n`" admits `i = −1`, and the frequency model divides by zero at a receiver's position. | Wording | Adopted.  The interface states `0 ≤ i, j < n`, the program's check rejects `−1`, and the requirements state the model's value 0 at a receiver's position and that the program keeps such boxes. |
| 17. `f` names the flattening and the carrier frequency, `JD` is not defined, and "in the frame of `R3(θ)`" is ambiguous. | Wording | Adopted: `f₀` for the frequency, `julian` of the frames model, and the sentence on `−ω ẑ × r`. |
| 18. M1 needs the Euclidean distance written out, since Mathlib's norm on `ℝ × ℝ × ℝ` is the maximum. | Wording | Adopted.  The model writes the square root of the sum of squares, and M1 takes the coordinates as functions. |
| 19. The range of 28,900 km holds for the nominal Galileo orbit, while Galileo 5 and 6 reach 25,900 km altitude, a range of 31,642 km, and 49 m. | Wording | Adopted. |

## Wrong programs

The reviewer's model carried each wrong program as a variant and ran it through the requirements' checks on the listed cases as the reviewer instantiated them and on cases of its own.  The table gives what rejected each in the reviewer's runs and, for each row that the listed cases missed, the case of the requirements' table that this response added for it.

| Wrong program | Listed cases | Added cases |
|---|---|---|
| Sign of a time or frequency difference; time difference without `/c`; frequency difference without `f₀` | Every case with consistent samples | — |
| `f₀` taken at `f_lo` | `aircraft`, by 11 of 26,721 samples | `f-wide-fine` |
| Receiver intervals collapsed to their centers | None | `wide-receiver-intervals`, `teme-wide-time` |
| Rotation term omitted, of the wrong sign, or with `ω = π/43200` | `teme` with frequency differences | `teme-fdoa`, `teme-fdoa-leo`, `teme-wide-time` |
| Polar motion in radians | `teme` | — |
| Polar rotations swapped; polar motion omitted | None | `teme-big-polar` |
| Receiver time at its lower end | None | `teme-wide-time` |
| Height at its lower end | None | `vertical-line` |
| Pruning or labeling 1 by the midpoint | Every case with consistent samples, or with label 1 | — |
| Every box split at the latitude; size in radians | Most cases, by status or size | — |
| Status 0 at the cap; truncation to `C` at the cap | `cap-four` | — |
| Final pass omitted, or without drops | None | `levels-zero-far`, the method check at status 2 |
| Latitude and longitude swapped in the output | Every case with boxes | — |
| Rejection treated as exclusion | `leo2-two-solutions`, by geometry | `ground-receiver` |
| One level too many | `levels-zero` | — |
| Never label 1 | None | `label-one-final`, `label-one-levels` |
| Geocentric latitude | Most cases | — |
| Status 2 at exactly `N` levels | None | `levels-exact` |
| Status 4 reported as 3, or ignored | None | `teme-status-four` |
| Region returned as one box at status 2 | Most cases, by status | — |
| Unused entries not checked for `F = 0`; length checked as a minimum; `i = −1` accepted | The invalid inputs | — |

| Wrong program that no listed case rejects | Reason, or an input that rejects it |
|---|---|
| The cap test `≥ C` | The output differs only when a level leaves exactly `C` boxes.  The reviewer's model found such a `C` for one case.  The module test against native Lean fixes the program's test. |
| Boxes of mark 2 split again | The boxes still cover.  Only the count differs, and only a cap between the two counts changes the status.  The module test fixes the program's step. |
| Strict inequalities in the test that a measurement holds | The labels differ only when a residual's interval ends exactly at `±ε`.  The module test fixes the comparisons. |
| Children in reversed order | The requirements now state the order, and the module test against native Lean fixes it. |

The listed cases reached 21 of 32 combinations of frames, kinds, statuses, marks, labels, caps, levels, and regions that the method distinguishes, and the reviewer's added cases 27.  The cases of the requirements' table reach the reviewer's missing combinations except a final label 1 at status 1.
