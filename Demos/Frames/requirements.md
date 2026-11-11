# Frames and time requirements

## Purpose and scope

The programs enclose standard-defined quantities of reference frames and time scales: the Greenwich mean sidereal time of 1982 that the TEME frame of SGP4 uses, the rotation of a TEME position into the Earth-fixed frame with polar motion, the conversion between Earth-fixed Cartesian and geodetic coordinates on the WGS 84 ellipsoid in both directions, and TAI, TT, and UT1 from UTC with a leap-second table.  Each program returns intervals with binary64 endpoints and a status, and a theorem states that an accepted result contains the real value of the formula that these requirements state.  Earth orientation parameters, the leap-second table, and every other datum enter as inputs, and the theorems take them as premises.  Converters that turn the IERS files into the inputs lie outside the theorems.

The first version leaves out the IAU 2006/2000A precession-nutation model, whose series have more than a thousand terms, the Earth rotation angle and the frames that the IAU 2000 resolutions define with it, the kinematic terms of the equation of the equinoxes, the transformation of velocities, TDB, UTC before 1972, and ellipsoids other than WGS 84.  The target is a ground program: a WebAssembly module of the verified compiler, whose C translation follows from the same compilation.

## Values and results

A float is a binary64 value, a word is a `UInt64`, and the real value of a float is the real number it represents.  An interval argument is a pair of floats `lo` and `hi`, accepted when both are finite and `lo ≤ hi`, and it stands for every real number between their values.  A theorem about an accepted result holds for every real point of every interval argument.  A day is a Modified Julian Date, the integer number of days since 1858 November 17 at 0 h, and a time of day is a number of seconds from the start of that day, which may lie outside `[0, 86400)` in the scales TAI, TT, and UT1.  The Julian date of the day `d` and the seconds `s` is `JD(d, s) = 2400000.5 + d + s/86400`.

| Quantity | Unit |
|---|---|
| Time of day, offsets between scales, UT1 − UTC | s |
| Angles of the sidereal time, latitude, and longitude | rad |
| Polar motion `xp`, `yp` | arcsecond, as IERS Bulletin A publishes it |
| Positions and heights | km |

Each export returns one status word followed by its values, and each interval value has the layout of [the interval library](../../Library/Numerics/Interval/README.md): its own status word, `lo`, and `hi`.  The flat results are `status, lo, hi` for `gmst`; `status` and three intervals for `temeToEcef`, `toCartesian`, and `toGeodetic`; and `status, dat` and three intervals for `timeScales`.  A result with status 0 holds accepted intervals.  A result with another status holds the rejected interval `1, 0, 0` in each interval and 0 in every other value.  The status of a result is the first row of its program's table whose condition holds, in the order of the table.

## Sidereal time

The model is the Greenwich mean sidereal time of Aoki et al. (1982) in the form of the function `gstime` of the code of Vallado, Crawford, Hujsak, and Kelso (AIAA 2006-6753), which the TEME frame of SGP4 uses.  With `T = (JD − 2451545)/36525` for the Julian date `JD` of UT1,

`θ(JD) = (2π/86400) · (67310.54841 + (876600 · 3600 + 8640184.812866) T + 0.093104 T² − 6.2·10⁻⁶ T³)`.

The code reduces `θ` to `[0, 2π)`, and SOFA's `iauGmst82` computes the same angle modulo 2π from the fraction of the day and the coefficient `24110.54841 − 43200`.  For a day `d` and seconds `s` of UT1, `86400 · 36525 T = 86400 (d − 51544) − 43200 + s`, so

`θ(JD(d, s)) = 2π (d − 51544) + (2π/86400) W(d, s)`,  with  `W(d, s) = s + 24110.54841 + T (8640184.812866 + T (0.093104 − 6.2·10⁻⁶ T))`

and `T = (d − 51544.5 + s/86400)/36525`.  The model `θ` is the first formula, and the identity is a theorem of the model.

```text
gmst  d : UInt64, lo, hi : Float  ->  status, lo, hi
```

`gmst` takes the day `d` and an interval of seconds of UT1 in that day.  It evaluates `W` on intervals in the grouping above, with each decimal constant as the interval of the quotient of two integers.  It computes the integer `n` below the midpoint of `W` divided by 86400, as the truncation `Float.toInt64` less one when the truncation exceeds the quotient, and returns `(W − 86400 n) · π/43200`, whose midpoint lies in `[0, 2π)` up to rounding.

| Status | Condition |
|---|---|
| 1 | `d ≥ 2³²`, or the interval of seconds is not accepted. |
| 2 | An interval operation rejected, `n` lies outside `±2⁵³`, or the result does not lie in `[−1, 7]`. |
| 0 | Otherwise.  Some integer `k` puts `θ(JD(d, s)) − 2πk` in the result for every `s` of the interval, and the result lies in `[−1, 7]`. |

## The Earth-fixed frame

The rotation of a position `r` in TEME into the Earth-fixed frame is

`r_E = R1(−yp) · R2(−xp) · R3(θ) · r`,

with `θ = θ(JD(d, s))` of UT1, `xp` and `yp` converted to radians by the factor `π/648000`, and the rotation matrices of SOFA's `iauRx`, `iauRy`, and `iauRz`:

| Matrix | Rows |
|---|---|
| `R1(α)` | `(1, 0, 0)`, `(0, cos α, sin α)`, `(0, −sin α, cos α)` |
| `R2(α)` | `(cos α, 0, −sin α)`, `(0, 1, 0)`, `(sin α, 0, cos α)` |
| `R3(α)` | `(cos α, sin α, 0)`, `(−sin α, cos α, 0)`, `(0, 0, 1)` |

`R3(θ)` takes TEME to the pseudo Earth-fixed frame, as equation 1 of AIAA 2006-6753 states.  `R1(−yp) R2(−xp)` is the transpose of the polar-motion matrix `W = R3(−s′) R2(xp) R1(yp)` of the IERS Conventions (2010), equation 5.3, with `s′ = 0`: it takes the terrestrial intermediate frame to the terrestrial frame, as SOFA's `iauPom00` computes it.  The function `teme2ecef` of Vallado's code differs in two ways.  It multiplies the polar-motion rotations in the other order, `R2(−xp) R1(−yp)`, which moves a position by about `|xp yp| |r|`, and after 1997 it can add the kinematic terms of the equation of the equinoxes, which these requirements leave out.

```text
temeToEcef  d : UInt64, s, xp, yp, x, y, z : interval  ->  status, x, y, z
```

`temeToEcef` computes the angle of `gmst`, without its test of the range, and applies the three rotations on intervals, with the sine and cosine of each interval angle from the library's enclosures.

| Status | Condition |
|---|---|
| 1 | `d ≥ 2³²`, or an interval argument is not accepted. |
| 2 | An interval operation rejected, or `n` lies outside `±2⁵³`. |
| 0 | Otherwise.  For every point of the arguments' intervals, the result's three intervals contain the components of `r_E`. |

## Geodetic coordinates

The ellipsoid is WGS 84 (NGA.STND.0036), with semimajor axis `a = 6378.137` km and flattening `f = 1/298.257223563`, `e² = f (2 − f)`, and `N(φ) = a/√(1 − e² sin²φ)`.  The Earth-fixed position of the latitude `φ`, the longitude `λ`, and the height `h` is

`x = (N + h) cos φ cos λ`,  `y = (N + h) cos φ sin λ`,  `z = (N (1 − e²) + h) sin φ`.

The geodetic coordinates of a point `(x, y, z)` are the triples `(φ, λ, h)` with `|φ| < π/2` and `N(φ) + h > 0` whose position is the point.  The second condition puts the point and its foot point on the ellipsoid in the same half meridian plane: without it, every point off the polar axis also has a triple with the longitude `λ + π` and `N + h < 0`.  Let `p = √(x² + y²)`.  The point lies in the domain `D` when `p > 0` and either `p > a e²` or `|z| > a e²/(1 − f)`, which excludes the polar axis and a cylinder about the center of radius 42.70 km and half-height 42.84 km.  A theorem of the model states that every point of `D` has geodetic coordinates, that their `φ` and `h` are unique, and that their `λ` is unique modulo 2π.

Uniqueness follows from two equations of the latitude.  The conditions give `p = (N + h) cos φ`, and eliminating `h` from the equations of `p` and `z` gives `p sin φ − z cos φ = e² N sin φ cos φ`.  With `u = tan φ` it becomes

`k(u) = p u − z − a e² u/√(1 + (1 − e²) u²) = 0`,

and `k` increases on the reals with slope at least `p − a e²`, so for `p > a e²` it has exactly one root, and every `u` lies within `|k(u)|/(p − a e²)` of it.  For `z > 0` and `v = cot φ` it becomes

`ℓ(v) = z v + a e² v/√(v² + 1 − e²) − p = 0`,

and `ℓ` increases with slope at least `z`, so it has exactly one root, within `|ℓ(v)|/z` of every `v`.  For `z > a e²/(1 − f)` no `φ` in `(−π/2, 0]` solves the equation of the latitude, since `e² N |sin φ| ≤ a e²/(1 − f)`, and points with `z < 0` follow by the symmetry `(φ, z) ↦ (−φ, −z)`.  Given the latitude, `h = p cos φ + z sin φ − a √(1 − e² sin²φ)`, and `λ` is any angle with `x = p cos λ` and `y = p sin λ`.

```text
toCartesian  lat, lon, h : interval  ->  status, x, y, z
toGeodetic   x, y, z : interval      ->  status, lat, lon, h
```

`toCartesian` evaluates the position formula on intervals.

| Status | Condition |
|---|---|
| 1 | An argument is not accepted. |
| 2 | An interval operation rejected. |
| 0 | Otherwise.  For every `(φ, λ, h)` of the arguments' intervals, the result contains the position. |

`toGeodetic` takes a box of points and computes `p` on intervals, with the interval of `x² + y²` clamped at zero, since outward rounding moves an exact zero one step below it.  When the lower end of `p` lies above zero, it chooses the equation in `u` if the midpoint of `p` is at least that of `|z|`, and the equation in `v` otherwise.  The equation in `v` takes `w = z`, or `w = −z` with the latitude negated at the end when the midpoint of `z` lies below zero.  The equation in `u` needs the lower end of `p − a e²` above zero, and the equation in `v` the lower end of `w − a e²/(1 − f)`.  Six Newton steps in binary64 from `u₀ = z/((1 − e²) p)` or `v₀ = (1 − e²) p/w` at the box's midpoint give an approximate root `ũ` or `ṽ`, whose accuracy no theorem uses.  The program encloses the residual `K` of `k(ũ)` or of `ℓ(ṽ)` over the box with `w` in place of `z`, and the slope bound `S` of `p − a e²` or of `w`, and returns `[ũ − m, ũ + m]` with `m = max(|K.lo|, |K.hi|)/S.lo` rounded up, which the bounds above show to contain the root of every point of the box.  The latitude is `arctan u`, or `π/2 − arctan v`, from the library's `atan` at the interval's ends, each moved two steps outward.  The height evaluates `(p + z u − a√(1 + (1 − e²) u²))/√(1 + u²)`, or `(p v + w − a√(v² + 1 − e²))/√(1 + v²)`, on the intervals.  The longitude is `2 arctan(y/(p + x))` when the midpoint of `x` is at least 0, and `π − 2 arctan(y/(p − x))` otherwise, each accepted when the interval of its divisor lies above zero.  The first formula gives angles in `(−π, π)` and the second in `(0, 2π)`.

| Status | Condition |
|---|---|
| 1 | An argument is not accepted. |
| 2 or 3 | The first of these in the order of the computation: the interval of `p` is rejected (2); its lower end is not above zero (3); the interval `p − a e²` or `w − a e²/(1 − f)` of the chosen equation is rejected (2); its lower end is not above zero (3); an interval operation of the root, the latitude, the height, or the longitude rejects, a divisor of the longitude does not lie above zero, or the longitude does not lie in `[−4, 7]` (2). |
| 0 | Otherwise.  Every point of the box lies in `D` and has geodetic coordinates `(φ, λ, h)` with `φ`, `λ`, and `h` in the result's intervals, and the longitude's interval lies in `[−4, 7]`. |

Status 3 also occurs for points of `D` with `a e² < p < a e²/(1 − f)` and `p < |z| ≤ a e²/(1 − f)`, which lie within 61 km of the Earth's center, since the program does not try the other equation.

## Time scales

A leap-second table lists, for each date from which TAI − UTC changed, the date and the new value of TAI − UTC, with the date to which the table is valid.  The IERS file `Leap_Second.dat` gives the entries and the sentence "File expires on 28 June 2027", whose date is the expiry `E`, MJD 61584, and the expiry line of `leap-seconds.list` gives the same date.  For the entries `(d₀, Δ₀), …, (dₙ₋₁, Δₙ₋₁)` with `d₀ < d₁ < ⋯ < dₙ₋₁` and `E > dₙ₋₁`, TAI − UTC on a day `d` with `d₀ ≤ d < E` is `ΔAT(d) = Δᵢ` for the largest `i` with `dᵢ ≤ d`.  A leap second ends a day, so the UTC day `d` lasts `L(d) = 86400 + ΔAT(d + 1) − ΔAT(d)` seconds, and a UTC time of that day has seconds `s` with `0 ≤ s < L(d)`.  For such a time the seconds of day `d` in the other scales are

| Scale | Seconds of day `d` | Source |
|---|---|---|
| TAI | `s + ΔAT(d)` | IERS Bulletin C |
| TT | `s + ΔAT(d) + 32.184` | IERS Conventions (2010) chapter 10 |
| UT1 | `s + δ`, with `δ = UT1 − UTC` at that time | IERS Bulletin A |

```text
timeScales  table : Array UInt64, d : UInt64, s : Float, dut1 : interval
            ->  status, dat : UInt64, tai, tt, ut1 : interval
```

The table holds `E, d₀, Δ₀, d₁, Δ₁, …` with `n ≥ 1` entries.  `timeScales` checks the table, and in the same pass over the entries it finds `ΔAT(d)` and `ΔAT(d + 1)`.  It computes `L(d)` in `Int64`, which holds every value that the table's bounds allow, and returns `ΔAT(d)` in `dat`.  TAI is the outward-rounded sum of `s` and `ΔAT(d)`, TT that sum plus the interval of `32184/1000`, and UT1 the sum of `s` and the interval `dut1`.  The value `s = −0` is accepted as zero.

| Status | Condition |
|---|---|
| 1 | The array's size is even or below 3, `E` or a date or offset is `2³²` or more, the dates do not increase strictly, or `E` is not above the last date. |
| 2 | `d < d₀`, or `d ≥ E − 1`. |
| 3 | `s` is not finite or lies outside `[0, L(d))`, or `dut1` is not accepted. |
| 4 | An interval operation rejected. |
| 0 | Otherwise.  The table is valid, `d₀ ≤ d` and `d + 1 < E`, `0 ≤ s < L(d)`, `dat = ΔAT(d)`, and the intervals contain the seconds of the table above for every `δ` in `dut1`. |

The test `d < E − 1` keeps `ΔAT(d + 1)` within the table and cannot wrap around, so the last day before the expiry is rejected.  Bulletin C 72 fixes TAI − UTC through 2027 June 30, so the rule is conservative by three days.

## Theorems

Each theorem has two layers.  The first concerns the model over the real numbers: the identity of `θ` with the form in `W`, the existence and uniqueness of geodetic coordinates in `D`, and the bounds on the roots of `k` and `ℓ`.  The second states that an accepted result of the program contains the model's value, as the status tables state.  The program's results with a nonzero status carry no theorem, and the tests require each expected status.  A theorem of the call of each export states that the WebAssembly module returns the Lean function's result without a trap.

## Tests

An oracle in Python with mpmath at 40 digits, written apart from the programs, evaluates `θ`, `r_E`, the position of geodetic coordinates, the geodetic coordinates of a point by its own iteration, and the time scales from the IERS table.  Its geodetic coordinates must satisfy `|φ| < π/2`, `N + h > 0`, and the position formula to 10⁻²⁰ km.  The oracle reproduces the values of SOFA's test suite for `iauGmst82`, `iauPom00` with its nonzero `s′`, `iauGc2gd`, `iauGd2gc`, `iauDat`, `iauUtctai`, `iauTaitt`, and `iauUtcut1`, which the ERFA distribution repeats, before it checks the programs.  The test runs the programs in native Lean and requires every accepted interval to contain the oracle's value, comparing the sidereal angle and the longitude modulo 2π.  It requires the midpoint of every accepted sidereal angle to lie in `[0, 2π]` and every longitude in the range of its formula, and it requires the statuses of the rejection cases.  For point arguments it bounds the widths:

| Program | Inputs | Width |
|---|---|---|
| `gmst` | MJD 15020 to 88069 | at most the increase of `θ` over the interval plus `10⁻¹¹` rad |
| `temeToEcef` | MJD 41317 to 66000, `\|xp\|, \|yp\| ≤ 0.5″` | at most `3·10⁻¹² \|r\| + 10⁻⁹` km for each coordinate |
| `toCartesian` | any | at most `10⁻⁹` km |
| `toGeodetic` | `max(p, \|z\|) ≥ 1000` km | at most `10⁻¹³` rad for the angles and `10⁻⁹` km for the height |
| `timeScales` | any | at most `10⁻⁹` s for TAI and TT |

The module test compares the WebAssembly module with native Lean bit for bit.

## References

- S. Aoki, B. Guinot, G. H. Kaplan, H. Kinoshita, D. D. McCarthy, and P. K. Seidelmann, [The new definition of universal time](https://ui.adsabs.harvard.edu/abs/1982A%26A...105..359A), Astronomy and Astrophysics 105, 1982, 359–361.
- D. A. Vallado, P. Crawford, R. Hujsak, and T. S. Kelso, [Revisiting Spacetrack Report #3](https://celestrak.org/publications/AIAA/2006-6753/), AIAA 2006-6753.
- G. Petit and B. Luzum (eds.), [IERS Conventions (2010)](https://www.iers.org/iers/en/publications/technicalnotes/tn36), IERS Technical Note 36.
- National Geospatial-Intelligence Agency, [World Geodetic System 1984](https://earth-info.nga.mil/index.php?dir=wgs84&action=wgs84), NGA.STND.0036.
- IERS Earth Orientation Centre, [Bulletin C and `Leap_Second.dat`](https://hpiers.obspm.fr/iers/bul/bulc/).
- IAU SOFA Board, [Standards of Fundamental Astronomy](https://www.iausofa.org/), and its BSD-licensed copy [ERFA](https://github.com/liberfa/erfa).
- [The interval library](../../Library/Numerics/Interval/README.md)
- [The SGP4 demo](../Sgp4/README.md)
