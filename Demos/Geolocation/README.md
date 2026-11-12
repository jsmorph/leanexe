# Emitter geolocation

[The program](Program.lean) locates a radio emitter from time differences and frequency differences of arrival at several receivers, with bounded measurement errors.  It searches a region of geodetic latitude, longitude, and height by interval branch-and-prune and returns boxes that hold every position of the region whose model values fit the measurements within their bounds, for some receiver states in the caller's intervals and some carrier frequency in its interval.  It labels a box 1 when every point of it fits for every such choice.  The receivers' states come in the Earth-fixed frame, or in the TEME frame of SGP4 at each receiver's time, which the program rotates into the Earth-fixed frame with [the frames demo's](../Frames/README.md) sidereal time, rotation, and polar motion.  [The requirements](requirements.md) define the model, the interface, and the method, and [the review](review.md) records the decisions, an independent review of the requirements, and the response to each finding.

[`verified_compile`](Verified.lean) compiles the program, with the interval operations, the library's `sin` and `cos`, and the frames demo's sidereal angle, rotation, and WGS 84 position, into one module, `geolocation`, of 34,367 bytes.  The module agrees with native Lean bit for bit on 33 cases.  An oracle in mpmath, written apart from the program, checks the module on 64 cases, 31 of them invalid inputs, against 756,839 consistent samples drawn for seven parameters of each valid case.  This is candidate 6.4 of the space-operations plan.  A Krawczyk test of existence or uniqueness within a box is left for a later iteration.

## Example

An emitter on the ellipsoid at 35° N, 40° E is seen by four receivers at 23,222 km altitude, the altitude of the Galileo satellites, in the Earth-fixed frame.  The input gives three time differences with bounds of 1 μs and three frequency differences with bounds of 0.5 Hz, all against receiver 0, a carrier in `[406.0, 406.1]` MHz, the region of ±2° about the emitter at height 0, `r = 0.2` km, `N = 60`, and `C = 65536` (the case `meo4-both` of the tests).  The module returns status 0 after 24 levels and 931 box tests, with 100 boxes labeled 0 that together span latitudes from 34.99317° to 35.00391° and longitudes from 39.99024° to 40.01758°, 1.2 km by 2.5 km on the ground.  Every position of the region whose model values fit the six measurements for some receiver state and carrier in their intervals lies in one of the 100 boxes.  With bounds of 20 μs for the time differences alone (`label-one-levels`), 275 of 977 boxes are labeled 1, and every point of those fits every admissible parameter.

## The model

The emitter sits at rest on the rotating Earth at `P(φ, λ, h)`, the WGS 84 position of the frames demo (`Demos.Frames.Model.position`).  A receiver `i` has the Earth-fixed position `sᵢ` and the velocity `uᵢ` relative to the rotating Earth, `ρᵢ(x)` is the Euclidean distance from `sᵢ` to `x`, and `ρ̇ᵢ(x) = (sᵢ − x) · uᵢ / ρᵢ(x)` is its rate.  A time difference of arrival at `i` less `j` has the model `(ρᵢ − ρⱼ) / c`, and a frequency difference the first-order Doppler model `−f₀ (ρ̇ᵢ − ρ̇ⱼ) / c`, with `c = 299792.458` km/s and the carrier frequency `f₀`.  A position fits the measurements for a parameter when each model lies within its bound `εₖ` of its measured value.

A parameter is a choice of each receiver's state and of `f₀` in the caller's intervals.  For the TEME frame it is a choice of each receiver's time `tᵢ` of UT1, TEME position `rᵢ`, and velocity `vᵢ`, and of one polar motion `xp`, `yp`, and the Earth-fixed state is `sᵢ = E(θ(tᵢ)) rᵢ` and `uᵢ = E(θ(tᵢ)) (vᵢ + ω(tᵢ) (rᵢ,₂, −rᵢ,₁, 0))`, with `E(θ) = R1(−yp) R2(−xp) R3(θ)`, the sidereal angle `θ` of GMST 1982, and its rate `ω`.  [The requirements](requirements.md#what-the-model-leaves-out) give the sizes of what the model leaves out: the light time and the rotation of the Earth during it, the atmosphere, terms of second order in `v/c`, the gravitational shift, and the emitter's motion.

## Method

The program computes in [interval arithmetic](../../Library/Numerics/Interval/README.md) with outward rounding.  The test of a box encloses `P` over the box, and for each measurement the residual, model less measured value, over the box and every parameter.  A measurement excludes the box when the residual's interval lies above `εₖ` or below `−εₖ`, and it holds over the box when the interval lies in `[−εₖ, εₖ]`.  A rejected interval does neither.  The test gives 0 when some measurement excludes the box, 2 when all hold over it, and 1 otherwise.

Each of `N` levels tests the untested boxes, drops those whose test gives 0, keeps those whose test gives 2 with mark 2, and splits each other box at the middle of its longest side when its size exceeds the resolution `r`, or keeps it with mark 1.  The size is the largest of `a Δφ`, `a c Δλ` with `c` the largest `|cos φ|` of the box, and `Δh`.  The search starts from the region as one box, stops with status 1 when a level would leave more than `C` boxes, and with status 0 when a level leaves no untested box.  A final pass tests the boxes left untested, drops those whose test gives 0, and labels each kept box 1 when its mark or its test is 2.

## Interface

```text
input   index              value                                   requirement
        0                  version                                 1
        1                  frame F                                 0 Earth-fixed, 1 TEME
        2, 3               receivers n, measurements m             whole, 2 ≤ n ≤ 16, 1 ≤ m ≤ 64
        4                  day d (MJD), F = 1                      whole, 0 ≤ d < 2^32
        5..8               xp, yp (arcsec) intervals, F = 1        ordered
        9, 10              carrier frequency interval (Hz)         0 < f_lo ≤ f_hi
        11..16             φ0, φ1 (rad), λ0, λ1 (rad), h0, h1 (km) ordered
        17                 resolution r (km)                       r > 0
        18, 19             levels N, cap C                         whole, 0 ≤ N ≤ 128, 1 ≤ C ≤ 65536
        20 + 14i ..        receiver i: t (s of UT1, F = 1),        each interval ordered
                           position (km), velocity (km/s)
        20 + 14n + 5k ..   measurement k: kind (1 time,            0 ≤ i, j < n, i ≠ j, ε ≥ 0
                           2 frequency), i, j, value, bound ε
        Every value is finite, and the array holds exactly 20 + 14n + 5m values.

output  0                  status: 0 complete, 1 stopped at C, 2 stopped after N levels,
                           3 invalid input (3, 0, 0, 0), 4 rejected receiver intervals (4, 0, 0, 0)
        1                  K, the number of boxes
        2                  box tests
        3                  levels completed
        4 + 7j ..          box j: φ from, φ to, λ from, λ to, h from, h to, and 1 when every
                           point fits every parameter
```

## Parts

| Part | File | Content |
|---|---|---|
| Model | [`Model.lean`](Model.lean), [`Rotation.lean`](Rotation.lean), [`Derivatives.lean`](Derivatives.lean) | The distances, the range rate, the two measurement models, the sidereal rate, the Earth-fixed velocity of a TEME state, and M1 to M3 |
| Enclosures | [`Spec.lean`](Spec.lean) | The residuals, the sidereal rate, and the Earth-fixed velocity as `enclosure_def` declarations, with their equations with the model |
| Program | [`Program.lean`](Program.lean), [`Flat.lean`](Flat.lean) | The receivers' states, the box test, the split rule, the levels, the final pass, the input check, and `locate` |
| Proofs | [`Search.lean`](Search.lean), [`Soundness.lean`](Soundness.lean) | The search for any box test with two facts, the receivers, the box test, and G1 to G5 |
| Module | [`Verified.lean`](Verified.lean), [`Call.lean`](Call.lean), [`File.lean`](File.lean) | The compilation, C1, and the file theorems |

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/geolocation/Axioms.lean) reports.  For an input `xs`, `Admissible xs P` states that the parameter `P` arises from the input's intervals, `Fits xs P x` that the position `x` fits the measurements for `P`, `Consistent xs φ λ h` that `P(φ, λ, h)` fits for some admissible `P`, `InRegion` that a triple lies in the region, `Returned out φ λ h` that it lies in a box of the output, and `HasStatus out s` that the output's status is `s`.

| Code | Theorem | File | Statement |
|---|---|---|---|
| M1 | `range_hasDerivAt` | [Model](Model.lean) | For a receiver whose coordinates have the derivatives `u` at `t` and whose position differs from `x`, the derivative of its distance to `x` is the range rate. |
| M2 | `earthFixed_hasDerivAt` | [Derivatives](Derivatives.lean) | For a TEME trajectory with derivative `v` at `t` and a sidereal angle with derivative `ω`, each coordinate of `E(θ) r` has as derivative that coordinate of `earthVelocity`. |
| M3 | `gmst_hasDerivAt` | [Derivatives](Derivatives.lean) | The rate `spin d t` is the derivative of the frames demo's sidereal angle `gmst82 (julian d t)` in the seconds `t` of UT1. |
| | `tdoaRes.encloses`, `fdoaRes.encloses`, `spin.encloses`, `earthVel.encloses`, `tdoaRes_eq`, `fdoaRes_eq`, `earthVel_eq` | [Specification](Spec.lean) | Each interval program encloses its real function, which equals the model's. |
| | `level_inv`, `search_inv`, `search_status`, `finalBoxes_spec` | [Search](Search.lean) | For any box test whose result 0 excludes a target set and whose result 2 gives a property of the box, the boxes of every level and of the final pass cover the target set in the region, keep their marks' properties, and number at most `C`. |
| | `receivers_sound`, `boxTest_spec` | [Soundness](Soundness.lean) | The receivers' intervals enclose every admissible parameter's Earth-fixed states, in both frames, so a box whose test gives 0 holds no consistent position and every position of a box whose test gives 2 fits every admissible parameter. |
| G1 | `locate_cover` | [Soundness](Soundness.lean) | For a valid input whose status is not 4, every triple of the region that is consistent lies in a returned box. |
| G2 | `locate_inner` | [Soundness](Soundness.lean) | For a valid input, every point of a box labeled 1 fits the measurements for every admissible parameter. |
| G3 | `locate_within` | [Soundness](Soundness.lean) | For a valid input, the output holds at most `4 + 7 C` values, and every box lies in the region. |
| G4 | `locate_status` | [Soundness](Soundness.lean) | For a valid input, the status is 0, 1, 2, or 4, and not 4 for the Earth-fixed frame.  At status 0 at most `N` levels are completed and every box labeled 0 is not split by `splits`, at status 1 fewer than `N` levels are completed, and at status 2 all `N`. |
| G5 | `locate_invalid` | [Soundness](Soundness.lean) | The status is 3 exactly when `valid xs` is false. |
| C1 | `locate_callSpec`, `locate_callBits`, `locate_call` | [Call](Call.lean) | Function 97, the export `locate`, called from a ready store with the bit patterns of `xs` borrowed and room for `top` to rise by `compiled.locate.bound xs` bytes, returns without a trap a new array that holds the bit patterns of `locate xs`.  The module's bytes decode to the module, and its start store is ready. |
| | `compiled.bytes`, `geolocation_file`, `geolocation_file_decode` | [Compilation](Verified.lean), [file theorems](File.lean) | `encode compiled.module` succeeds with bytes that decode to the module, and `build/verified/geolocation.wasm` holds them. |

The proofs of [`Search.lean`](Search.lean) hold for any box test with the two facts (`TestSound`), and [`Soundness.lean`](Soundness.lean) supplies them from the enclosures of the receivers' states, the position, and the residuals.  The searches reuse the screening demo's loop lemmas `loop_cover` and `loop_size_le`.

## Tests

`tests/verified/run.sh --cases geolocation` writes the module, validates it, compares `locate` with native Lean on [the module cases](../../tests/TestSupport/Geolocation/Cases.lean), runs [the axiom audit](../../tests/geolocation/Axioms.lean), and checks the file theorems.  The cases hold four receivers with time differences, frequency differences, and both, receiver intervals, an aircraft's heights, the whole Earth, a region without the emitter, a region at the pole, `N = 0`, `N = 10`, a cap of 4, rejected enclosures, receivers in the TEME frame with and without time intervals and with a time that gives status 4, invalid inputs, and 6 inputs from a linear congruential generator.  All 33 cases agree with native Lean bit for bit, and the 30 theorems of the audit report only the three permitted axioms.

[The oracle](../../tests/geolocation/oracle.py) checks the module against dense sampling of the model, written apart from the program.  It evaluates the position, the distances, the range rates, and the two measurement models with its own formulas, in binary64 and in mpmath at 30 digits for every sample within `10⁻⁹` of a bound, and for the TEME frame it computes the sidereal angle from the GMST 1982 polynomial, rotates with its own matrices, and differentiates the rotated position numerically for the velocity.  For each case it takes seven parameters, the centers of the intervals, the parameter that produced the measurements, three random ones, and two random corners, and for each it covers the region by a Lipschitz subdivision down to the resolution and samples a grid of 4 points along each side of every remaining cell.  [The requirements](requirements.md#tests) list its checks and the cases with their inputs and expected results: the status, the counts, every consistent sample in a returned box, every sampled point of a box labeled 1 fitting every parameter, the size rule and disjoint boxes at status 0, and the method's bound on every box's center.  [The harness](../../tests/geolocation/locate.mjs) calls the module under Node in a fresh instance for each case.

```sh
uv run tests/geolocation/oracle.py build/verified/geolocation.wasm --mutate
```

All 64 cases pass: the 33 valid ones with the statuses, counts, and labels that [the requirements](requirements.md#tests) state, 9 of them with boxes labeled 1, and the 31 invalid ones with `3, 0, 0, 0`.  The valid cases give 3,811,316 samples, of which 756,839 are consistent for their parameter and lie in a returned box, and mpmath decides every sample within `10⁻⁹` of a bound.  The mutation run makes 174 altered outputs, each wrong by construction, and the checks reject all of them, among them a small box added at a corner of the region in each of the 25 cases where no box holds that corner, which the method's bound rejects in every one.  The review's model ran its 39 wrong programs through checks of the same kinds, and [the review](review.md#wrong-programs) lists the cases that reject each.

## Cost

`uv run tests/geolocation/oracle.py build/verified/geolocation.wasm --cost` times each call as the median of nine calls in Node 24.13 on a four-core AArch64 virtual machine.  A box test takes about 2.5 µs with two measurements and 4.8 µs with six.

| Cases | Box tests | ms |
|---|---|---|
| Four receivers at 23,222 km, ±2° at 0.2 km, either kind or both, either frame | 901 to 2,217 | 3.2 to 9.2 |
| The whole Earth at 1 km | 785 | 4.0 |
| The pole, and the antimeridian with longitudes `−π` to `π` | 743 to 869 | 3.8 to 4.3 |
| An aircraft with heights 0 to 12 km at 0.25 km | 19,227 | 93.2 |
| Three receivers at 800 km with frequency differences of 0.1 Hz at 0.02 km | 20,187 to 20,283 | 62.7 to 62.8 |
| Two receivers at 800 km in one orbit, ±10° at 0.2 km | 105,657 | 256.7 |

The cost grows with the area of the region in which the residuals' enclosures stay within the bounds, so two receivers, wide receiver intervals, and fine resolutions cost the most.

## Limits

The theorems concern the stated model: an emitter at rest on the rotating Earth, instantaneous distances, the first-order Doppler shift, the receivers' intervals, and for the TEME frame the frames demo's GMST 1982 and polar-motion rotation with the polar motion constant over the receivers' times.  The light time, the atmosphere, the relativistic terms, the emitter's motion, the conversion of measurements from a ground station to the receivers, and the receivers' intervals are the caller's premises, and [the requirements](requirements.md#what-the-model-leaves-out) give their sizes.  The theorems bound no width and no count: an output that returns the region as one box labeled 0 satisfies G1 to G3, and a box labeled 0 may hold no consistent position, since interval evaluation overestimates a residual's range.  No theorem states that the boxes do not overlap or their order, which the tests and the module comparison check.  C1 states the generated allocation bound `compiled.locate.bound`, for which no closed form is proved, and no test covers a C translation or an AArch64 image.  `verified_compile` of the module takes 32 minutes at three threads and a peak of 6.0 GB.  The search costs most where the residuals change slowly over the region, as with two receivers or wide intervals.

## References

- [Emitter geolocation requirements](requirements.md)
- [Emitter geolocation: decisions and review](review.md)
- Cospas-Sarsat, [Introduction to the Cospas-Sarsat system](https://www.cospas-sarsat.int/en/system/overview)
- D. A. Vallado, P. Crawford, R. Hujsak, and T. S. Kelso, [Revisiting Spacetrack Report #3](https://celestrak.org/publications/AIAA/2006-6753/), AIAA 2006-6753
- [The frames and time demo](../Frames/README.md)
- [The conjunction screening demo](../Screening/README.md)
- [The interval library](../../Library/Numerics/Interval/README.md)
