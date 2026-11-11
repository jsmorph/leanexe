# Frames and time

The programs enclose quantities of reference frames and time scales that other space programs need: the Greenwich mean sidereal time of 1982, which defines the TEME frame of [SGP4](../Sgp4/README.md), the rotation of a TEME position into the Earth-fixed frame with polar motion, the conversion between Earth-fixed Cartesian and geodetic coordinates on the WGS 84 ellipsoid in both directions, and TAI, TT, and UT1 from UTC with a leap-second table.  Each returns intervals with binary64 endpoints and a status, and a theorem states that the intervals of an accepted result contain the value of a model over the real numbers.  Earth orientation parameters and the leap-second table are inputs, and the theorems take them as premises.  [The requirements](requirements.md) define every quantity, and [the review](review.md) records the decisions and an independent review of the requirements.

[`verified_compile`](Verified.lean) compiles the five programs, with the library's `sin`, `cos`, and `atan` and [the interval layer](../../Library/Numerics/Interval/README.md), into one module, `frames`, of 24,180 bytes.  The module agrees with native Lean bit for bit on 55 cases, and an oracle in mpmath, which first reproduces the values of SOFA's test suite, finds its value in every accepted interval of 1,117 cases.

## Example

The test point of SOFA's `iauGc2gd` lies at `x = 2000` km, `y = 3000` km, and `z = 5244` km.  `toGeodetic` with the point intervals of these values returns status 0 and the intervals of the table, and SOFA's test values lie in each.

| Coordinate | Lower endpoint | Upper endpoint | SOFA's test value |
|---|---|---|---|
| Latitude (rad) | 0.9716018481907537 | 0.9716018481907557 | 0.97160184819075459 |
| Longitude (rad) | 0.9827937232473283 | 0.9827937232473298 | 0.9827937232473290680 |
| Height (km) | 0.33141724613363277 | 0.3314172461509075 | 0.3314172461426059892 |

`gmst` of MJD 53736 at 0 h UT1 returns `[1.7541749818604984, 1.7541749818608643]`, which holds the value 1.754174981860675096 of SOFA's test of `iauGmst82`.

## Parts

| Part | File | Content |
|---|---|---|
| Model | [`Model.lean`](Model.lean) | The sidereal time, the rotations, the position of geodetic coordinates, the definition of geodetic coordinates and of the domain `D`, and TAI − UTC from a table, over the real numbers |
| Geodetic theorems | [`Geodetic.lean`](Geodetic.lean) | The two equations of the latitude, their growth bounds, roots, and a posteriori bounds, and the existence and uniqueness of geodetic coordinates |
| Interval forms | [`Enclose.lean`](Enclose.lean) | The formulas as `enclosure_def` declarations, the enclosure of `arctan`, and their equality with the model |
| Programs | [`Program.lean`](Program.lean), [`Time.lean`](Time.lean) | `gmst`, `temeToEcef`, `toCartesian`, `toGeodetic`, and `timeScales` |
| Soundness | [`Soundness.lean`](Soundness.lean), [`TimeSound.lean`](TimeSound.lean) | What an accepted result of each program states |
| Compilation | [`Verified.lean`](Verified.lean), [`Call.lean`](Call.lean), [`File.lean`](File.lean) | The module, the call theorems, and the file theorems |

## Interface

```text
gmst         d : UInt64, lo, hi                 ->  status, lo, hi
temeToEcef   d : UInt64, s, xp, yp, x, y, z      ->  status, x, y, z
toCartesian  lat, lon, h                         ->  status, x, y, z
toGeodetic   x, y, z                             ->  status, lat, lon, h
timeScales   table : Array UInt64, d : UInt64, s, dut1  ->  status, dat, tai, tt, ut1
```

Every argument other than a day, a table, and the UTC seconds of `timeScales` is an interval, given as two floats `lo ≤ hi`, and every result interval has its own status word, `lo`, and `hi`.  A day is a Modified Julian Date, seconds count from the start of that day, angles are in radians, polar motion in arcseconds, and lengths in km.  The table of `timeScales` holds the expiry `E` and the pairs of a date and TAI − UTC, which the IERS file `leap-seconds.list` gives with dates in seconds from 1900.  [The requirements](requirements.md#values-and-results) state each status.

| Program | Status 0 | Other statuses |
|---|---|---|
| `gmst` | The sidereal angle less one whole number of turns, in `[−1, 7]` | 1 an invalid day or interval; 2 a rejected operation or a result outside `[−1, 7]` |
| `temeToEcef` | The Earth-fixed position of every point | 1 an invalid input; 2 a rejected operation |
| `toCartesian` | The position of every geodetic coordinate | 1 an invalid input; 2 a rejected operation |
| `toGeodetic` | Geodetic coordinates of every point of the box, which lies in `D` | 1 an invalid input; 2 a rejected operation or a longitude outside `[−4, 7]`; 3 a box that the tests do not show in `D` |
| `timeScales` | TAI − UTC, and the seconds of the day in TAI, TT, and UT1 | 1 a malformed table; 2 a day outside `[d₀, E − 1)`; 3 invalid seconds or UT1 − UTC; 4 a rejected operation |

## Method

**Sidereal time.**  The model is GMST 1982 in the form of the function `gstime` of AIAA 2006-6753.  For a day `d` and seconds `s` of UT1 it equals `2π (d − 51544)` plus `W(d, s) · π/43200`, with `W = s + 24110.54841 + T (8640184.812866 + T (0.093104 − 6.2·10⁻⁶ T))` and `T = (d − 51544.5 + s/86400)/36525`, which `gmst82_eq` proves.  The program evaluates `W` on intervals, subtracts 86400 times the floor of its midpoint over 86400, which `Float.toInt64` and a correction give, and multiplies by `π/43200`.  The integer day keeps the large term exact, and the angle's interval for a point of UT1 has a width of at most `2.4·10⁻¹²` rad for dates from 1900 to 2100.

**The Earth-fixed frame.**  The position is `R1(−yp) R2(−xp) R3(θ) r`, with SOFA's rotation matrices: `R3(θ)` takes TEME to the pseudo Earth-fixed frame, as AIAA 2006-6753 states, and `R1(−yp) R2(−xp)` is the transpose of the polar-motion matrix `W` of the IERS Conventions (2010) with `s′ = 0`, which SOFA's `iauPom00` computes.  The rotation depends on the angle only through its sine and cosine, so the whole turns of `gmst` drop out (`toEarth_periodic`).

**Geodetic coordinates.**  The geodetic coordinates of a point are the triples `(φ, λ, h)` with `|φ| < π/2` and `N(φ) + h > 0` whose WGS 84 position is the point.  Off the polar axis, the latitude solves `k(u) = p u − z − a e² u/√(1 + (1 − e²) u²) = 0` with `u = tan φ` and `p = √(x² + y²)`, and for `z > 0` also `ℓ(v) = z v + a e² v/√(v² + 1 − e²) − p = 0` with `v = cot φ`.  `k` rises with slope at least `p − a e²` and `ℓ` with slope at least `z` (`growthA`, `growthB`), from algebraic monotonicity lemmas, so each has exactly one root when its slope bound is positive (`bijective_of_growth`), and every argument lies within its residual over the slope bound of the root (`bound_of_growth`).  The domain `D`, where `p > 0` and either `p > a e²` or `|z| > a e²/(1 − f)`, is the union of the two equations' domains and leaves out the polar axis and a cylinder of 42.70 km by 42.84 km about the center.

`toGeodetic` chooses `k` when the midpoint of `p` is at least that of `|z|`, and `ℓ` otherwise, with `z` negated below the equator.  Six Newton steps in binary64 give an approximate root, whose accuracy no proof uses: the program encloses its residual over the box and widens it by the residual's magnitude over the lower end of the slope bound, which contains the root of every point of the box.  The latitude is `arctan u` or `π/2 − arctan v` from the library's `atan` with two outward steps (`arctan.encloses`), the height follows from the latitude, and the longitude is `2 arctan(y/(p + x))` or `π − 2 arctan(y/(p − x))`.  `toCartesian` evaluates the position formula on intervals.

**Time scales.**  TAI − UTC on day `d` is the offset of the last entry whose date is at most `d`.  One pass over the table checks that its values lie below `2³²` and its dates increase, and finds TAI − UTC on `d` and on `d + 1`, whose difference gives the length of the UTC day `d`, 86401 s on the day of a positive leap second.  The program accepts UTC seconds in `[0, L(d))` and days with `d₀ ≤ d < E − 1`, and returns TAI as `s + ΔAT(d)`, TT as TAI plus the interval of `32184/1000`, and UT1 as `s` plus the interval of UT1 − UTC.  The UT1 interval is the input of `gmst` and `temeToEcef`.

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/frames/Axioms.lean) reports.  The real value of a float is the real number that it represents, `Within lo hi x` states that `x` lies between the values of `lo` and `hi`, and `Contains i x` that the interval `i` is accepted, has finite endpoints, and holds `x`.

| Theorem | File | Statement |
|---|---|---|
| `gmst82_eq`, `turns_eq` | [`Enclose.lean`](Enclose.lean) | `θ(JD(d, s)) = 2π (d − 51544) + W(d, s) · π/43200`, so `(W − 86400 n) · π/43200` is `θ` less `2π (d − 51544 + n)`. |
| `toEarth_eq`, `toEarth_periodic` | [`Enclose.lean`](Enclose.lean) | The interval form of the rotation is `Model.earthFixed`, `R1(−yp) R2(−xp) R3(ψ)`, and depends on `ψ` only modulo 2π. |
| `growthA`, `growthB` | [`Geodetic.lean`](Geodetic.lean) | `k` rises by at least `(p − a e²)` times the distance, and `ℓ` by at least `z` times it. |
| `bijective_of_growth`, `bound_of_growth` | [`Geodetic.lean`](Geodetic.lean) | A continuous function that rises with a positive slope bound `s` takes every value once, and every `x` lies within `\|g x\|/s` of its root. |
| `geodetic_exists` | [`Geodetic.lean`](Geodetic.lean) | Every point of `D` has geodetic coordinates. |
| `geodetic_unique` | [`Geodetic.lean`](Geodetic.lean) | Two sets of geodetic coordinates of a point of `D` have the same latitude and height, and longitudes with the same cosine and sine. |
| `arctan.encloses` | [`Enclose.lean`](Enclose.lean) | The interval of `atan` at the endpoints, two steps outward, holds the arctangent of every point. |
| `gmst_sound` | [`Soundness.lean`](Soundness.lean) | An accepted result has `d < 2³²`, finite ordered arguments, and finite endpoints in `[−1, 7]`, and one integer `k` puts `θ(JD(d, s)) − 2πk` in it for every `s` of the argument's interval. |
| `temeToEcef_sound` | [`Soundness.lean`](Soundness.lean) | The intervals of an accepted result contain the components of `Model.earthFixed (θ(JD(d, s))) xp yp r` for every `s`, `xp`, `yp`, and `r` of the arguments' intervals. |
| `toCartesian_sound` | [`Soundness.lean`](Soundness.lean) | The intervals of an accepted result contain `Model.position φ λ h` for every `φ`, `λ`, and `h` of the arguments' intervals. |
| `toGeodetic_sound` | [`Soundness.lean`](Soundness.lean) | Every point of the box of an accepted result lies in `D` and has geodetic coordinates in the result's intervals, and the longitude's interval lies in `[−4, 7]`. |
| `timeScales_sound` | [`TimeSound.lean`](TimeSound.lean) | An accepted result has a valid table, `d₀ ≤ d` and `d + 1 < E`, `dat` equal to TAI − UTC on day `d` by `Model.LeapOffset`, UTC seconds in `[0, L(d))`, and intervals that contain `s + ΔAT(d)`, `s + ΔAT(d) + 32.184`, and `s + δ` for every `δ` of the interval of UT1 − UTC. |
| `compiled.gmst.implements` and its siblings | [`Verified.lean`](Verified.lean) | The module's exports return the words of the Lean functions' results. |
| `gmst_call`, `temeToEcef_call`, `toGeodetic_call`, `toCartesian_call`, `timeScales_call`, `frames` | [`Call.lean`](Call.lean) | The module's bytes decode to the module, whose start store is ready and whose exports, functions 82 to 86, return the Lean functions' results without a trap from every ready store. |
| `frames_file`, `frames_file_decode` | [`File.lean`](File.lean) | `build/verified/frames.wasm` holds `encode compiled.module` and decodes to `compiled.module`. |

## Tests

`tests/verified/run.sh --cases frames` writes the module, validates it, compares every export with native Lean on [the cases](../../tests/TestSupport/Frames/Cases.lean), runs [the axiom audit](../../tests/frames/Axioms.lean), and checks the file theorems.  All 55 cases agree bit for bit, among them every rejecting status of each program.

[`tests/frames/run.sh`](../../tests/frames/run.sh) runs the containment test.  [The oracle](../../tests/frames/oracle.py) evaluates the model in mpmath at 40 digits, apart from the programs: the sidereal time from `gstime`'s polynomial, the rotations from SOFA's matrices, the geodetic coordinates of a point by the fixed-point iteration `φ = atan2(z + e² N sin φ, p)`, and TAI − UTC by a binary search of the IERS's [`leap-seconds.list`](../../tests/frames/leap-seconds.list).  It first reproduces the values of SOFA's test suite for `iauGmst82`, `iauPom00`, `iauGc2gd`, `iauGd2gc`, `iauDat`, `iauUtctai`, `iauTaitt`, and `iauUtcut1`, from ERFA's copy of the suite, and requires its geodetic coordinates to satisfy `|φ| < π/2`, `N + h > 0`, and the position formula.  For each accepted result it samples the corners and 16 random points of the arguments' intervals and requires the oracle's value in the result, comparing angles modulo 2π, the sidereal angle's midpoint in `[0, 2π]`, and each longitude in the range of its formula.  For each case of the review's list it requires the stated status.

| Program | Cases | Largest width for point arguments |
|---|---|---|
| `gmst` | 215 | 2.4·10⁻¹² rad, MJD 15020 to 88069 |
| `temeToEcef` | 156 | 1.2·10⁻¹² times `\|r\|` |
| `toCartesian` | 158 | 5.1·10⁻¹¹ km |
| `toGeodetic` | 285 | 2.5·10⁻¹⁵ rad in latitude, 5.4·10⁻¹⁵ rad in longitude, 1.4·10⁻¹⁰ km in height, for `max(p, \|z\|) ≥ 1000` km |
| `timeScales` | 303 | 5.9·10⁻¹¹ s in TAI and TT |

The cases cover dates from 1900 to 2100, polar motion up to 10″, positions of low, navigation, and geostationary orbits, latitudes near both poles and on the equator, longitudes across the negative x-axis, points within 61 km of the center, every leap second of the table with the seconds 86400.5 and 86400.999999 of the day that ends with it, the day before the expiry, and malformed tables.  All pass.

## Limits

The theorems relate the programs to the formulas of [the requirements](requirements.md), and the formulas' agreement with their sources rests on the oracle and the review.  GMST 1982 and the pseudo Earth-fixed frame are those of SGP4's TEME frame: the true orientation of the Earth differs from them by nutation and the other terms of the IAU 2006/2000A model, which the programs leave out.  The function `teme2ecef` of the SGP4 code multiplies the polar-motion rotations in the other order and can add the kinematic terms of the equation of the equinoxes, so its positions differ from `temeToEcef`'s by about `|xp yp| |r|` and by those terms.  The Earth orientation parameters, the leap-second table, and their error bounds are the caller's, and the converters that produce them lie outside the theorems.

`gmst` fixes the whole turns of its angle up to one: `[−1, 7]` holds the angle and possibly the angle plus or minus 2π.  The theorems bound no width.  `toGeodetic` rejects boxes on the polar axis and within the cylinder about the center, and also points of `D` with `a e² < p < a e²/(1 − f)` and `p < |z| ≤ a e²/(1 − f)`, within 61 km of the center, since it does not try the other equation.  `timeScales` rejects the last day before the table's expiry and UTC before 1972, and the programs transform no velocity.  The oracle reproduces SOFA's test values but is not SOFA itself, since `pyerfa`, which would run SOFA's algorithms, is not a dependency of the repository.  The C translation has its theorem but no native driver that builds and runs it.  `verified_compile` of the module takes 25 minutes at two threads and a peak of 5.8 GB.  The theorems rest on the verified compiler's trusted base, described in [the trusted-base document](../../docs/trusted-base.md).

## References

- [Frames and time requirements](requirements.md)
- [The review of the requirements](review.md)
- S. Aoki, B. Guinot, G. H. Kaplan, H. Kinoshita, D. D. McCarthy, and P. K. Seidelmann, [The new definition of universal time](https://ui.adsabs.harvard.edu/abs/1982A%26A...105..359A), Astronomy and Astrophysics 105, 1982, 359–361.
- D. A. Vallado, P. Crawford, R. Hujsak, and T. S. Kelso, [Revisiting Spacetrack Report #3](https://celestrak.org/publications/AIAA/2006-6753/), AIAA 2006-6753.
- G. Petit and B. Luzum (eds.), [IERS Conventions (2010)](https://www.iers.org/iers/en/publications/technicalnotes/tn36), IERS Technical Note 36.
- IERS Earth Orientation Centre, [Bulletin C and the leap-second files](https://hpiers.obspm.fr/iers/bul/bulc/).
- IAU SOFA Board, [Standards of Fundamental Astronomy](https://www.iausofa.org/), and its BSD-licensed copy [ERFA](https://github.com/liberfa/erfa).
- [The interval library](../../Library/Numerics/Interval/README.md)
- [The SGP4 demo](../Sgp4/README.md)
