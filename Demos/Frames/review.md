# Frames and time requirements: decisions and review

[The requirements](requirements.md) specify the first version of brief 5.2 of the space-operations candidates, as the plan that orders the candidates restricts it: the sidereal time of SGP4's frame, the conversion between Earth-fixed Cartesian and geodetic coordinates, and the offsets between time scales from a leap-second table, with Earth orientation parameters and the table as inputs.  This record gives each decision with its reason and the findings of a fresh agent's review of the requirements, with the verification and the response for each.  Each decision followed the standard procedure: the options, a recommendation, a review of the recommendation, and a revision.

## Decisions

| Question | Options | Choice | Reason |
|---|---|---|---|
| Location | A library under `Library/`; a demo beside the SGP4 demo | `Demos/Frames`, one module `frames` | The programs start from SGP4's frame and serve the other space candidates, such as event windows and emitter geolocation, which import demo modules as the CE and LE programs import the conjunction demo. |
| Rotation angle | The Earth rotation angle of IAU 2000; GMST 1982 | GMST 1982 in the form of `gstime` | The TEME frame of SGP4 is defined with GMST 1982.  The Earth rotation angle serves the CIO-based transformation, which comes with the IAU 2006/2000A model. |
| Representation of a time | A two-part Julian date, as SOFA's; a day word and seconds | A Modified Julian Date as a word and seconds as a float or an interval | The integer day separates `2π (d − 51544)` exactly from the angle, and the seconds of a UTC day with a leap second need no scaling. |
| Reduction of the angle | None; by the floor of the midpoint | The floor of the midpoint, from `Float.toInt64` with a correction, and a test that the result lies in `[−1, 7]` | The dialect has no floor of a float.  The theorem keeps a whole number of turns open, and the range test fixes it up to one turn. |
| Polar motion | None; the transpose of `W` of IERS (2010) eq. 5.3; Vallado's order | The transpose of `W` with `s′ = 0`, as SOFA's `iauPom00` | It is the convention of the IERS and of SOFA, the oracle the brief names.  The other order differs by about `\|xp yp\| \|r\|`. |
| Ellipsoid and unit | Ellipsoid parameters as inputs; WGS 84 fixed | WGS 84 in km | WGS 84 is the ellipsoid of the catalog's users, and km is the unit of SGP4's positions.  GRS 80 differs in the eleventh digit of `f`. |
| Inverse conversion | A closed form, such as Vermeille's or Heikkinen's; an iteration with an a posteriori bound | Newton steps on `k` or `ℓ`, widened by the residual over the slope bound | The slope bounds and the uniqueness follow from algebraic monotonicity lemmas.  A closed form needs a cube root, which the interval library lacks, and a proof of its algebra. |
| Longitude | An enclosure of `atan2` on a box; half-angle formulas with `atan` | The half-angle formulas | `atan` is monotone with a one-step theorem.  `atan2` is not monotone on a box. |
| Leap seconds | A table inside the program; a table as input | An input array with its expiry | The plan names the table as input, and the expiry keeps the program from extrapolating past the IERS's announcement. |
| Oracle | SOFA through `pyerfa`; mpmath code checked against SOFA's test values | Both | The mpmath model reproduces SOFA's test values and gives the exact values at every sampled point.  The user approved `pyerfa` as a test-only dependency of the oracle, which compares every accepted result with ERFA's routines within a bound on their binary64 error. |
| Target | Ground (WebAssembly, C); an AArch64 image | Ground | The programs are infrastructure for ground programs of the other candidates. |

## Review

A fresh agent reviewed the draft against the brief and the plan.  It built its own interval arithmetic, an mpmath oracle at 40 digits, and a model of the five programs from the requirements alone, and it ran no Lean.  Its oracle reproduced every value of ERFA's tests for `gmst82`, `gc2gd`, `gd2gc`, `pom00`, `dat`, `utctai`, `taitt`, and `utcut1`, and the model's accepted results contained the oracle's values on 10,205 cases.  Its scripts are in the agent's scratch directory, and the table gives each finding with its verification and response.

| Finding | Verification | Response |
|---|---|---|
| 1. The definition of geodetic coordinates admits a second triple with the longitude `λ + π` and `N + h < 0` for every point off the axis, so uniqueness fails and a program that returns the far side meets the theorem. | 300 of 300 random points; the far-side triple of SOFA's point | Adopted.  The definition requires `N(φ) + h > 0`, which `Model.IsGeodetic` states, and the uniqueness proof derives `p = (N + h) cos φ` from it.  The author found the same defect while writing the proof. |
| 2. "Widens the approximate root by their quotient" is ambiguous, and the interval quotient `ũ − K/S` misses the root at (42.75, 0, 5) km. | The reviewer's model at that point | Adopted: the text states `[ũ − m, ũ + m]` with `m = max(\|K.lo\|, \|K.hi\|)/S.lo` rounded up, which `widen` computes. |
| 3. `R1(−yp) R2(−xp)` is the transpose of `W` of eq. 5.3, and Vallado's `teme2ecef` uses the other order and may add the kinematic terms. | `check_sofa.py`; the sources of eq. 5.3, `pom00.c`, and `teme2ecef.m` | Adopted: the text names the transpose and both differences. |
| 4. The half-height of the excluded cylinder is 42.84 km. | `(a² − b²)/b = 42.8413` | Corrected. |
| 5. The status-0 statement of `gmst` admits results off by whole turns, and the tests did not say how angles are compared. | Two wrong programs pass a comparison modulo 2π | Adopted: `gmst` tests that its result lies in `[−1, 7]` and the longitude in `[−4, 7]`, the theorems state both, and the tests compare modulo 2π and check the ranges of the midpoints. |
| 6. The equation in `v` has no test of `p > 0`, so boxes on the axis get status 2. | Three boxes on the axis | Adopted: the program tests the lower end of `p` before it chooses an equation, with status 3.  The containment test then found that the square root still rejected boxes on the axis, whose interval of `x² + y²` outward rounding moves below zero, so the program clamps that interval at zero, and those boxes get status 3. |
| 7. No status precedence is stated. | Reading | Adopted: the first row that applies, in the order of each table. |
| 8. `d + 1` wraps at `d = 2⁶⁴ − 1`, and `L(d)` computed in unsigned words wraps when the offset drops by more than 86400. | Two wrong programs in the model | Adopted: the program tests `d < E − 1` and computes `L(d)` in `Int64`.  The author's proof of `timeScales_sound` failed on the first wraparound before the review reported it.  Both cases are tests. |
| 9. TT adds 32.184, not an integer. | Reading | Corrected: the text names the interval of `32184/1000`. |
| 10. The layout of the results is ambiguous. | Reading | Adopted: each export's flat result and the values of a rejected result are stated. |
| 11. No widths are stated, and some wrong programs differ only in width. | The model's widths | Adopted: the Tests section states bounds from the measurements of the program. |
| 12. The derivation of the expiry from the file and the place of the converter are unstated, and the rule `d + 1 < E` is conservative. | `Leap_Second.dat`, `leap-seconds.list`, Bulletin C 72 | Adopted: all three are stated. |
| 13. The oracle must take `s′` for SOFA's `pom00` test, add `utctai`, `taitt`, and `utcut1`, and select the near-side root. | The reviewer's oracle missed `pom00` without `s′` and first converged to the far side | Adopted: the oracle applies `R3(s′)`, reproduces the three time-scale tests, and checks `\|φ\| < π/2`, `N + h > 0`, and the forward residual. |
| 14. The choice of equation rejects points of `D` with `42.70 < p < 42.84` and `p < \|z\| ≤ 42.84`. | (42.75, 0, 42.80) | Declined.  The region lies within 61 km of the Earth's center, and a fallback to the other equation adds a branch to the program and its proof for no point of practical use.  The text states the region, and a test requires status 3 there. |
| 15. The height of the equation in `v` must use `\|z\|`. | A wrong program with the signed `z` | Corrected: the text names `w`, which is `z` or `−z`. |
| 16. No requirement forces a forbidden construct, and the floor must come from `Float.toInt64`. | `docs/verified-manual.md` | The text names the method. |
| 17. The link to the IERS Conventions returns 404. | `curl` | Corrected. |
| 18. Several paragraphs are short, and "near", "fix them", and "not odd and at least 3" are vague. | Reading against `CLAUDE.md` | Corrected. |
| 19. Lean files appeared while the review ran. | File times | The author drafted the model and the programs in parallel and revised them for findings 1, 2, 5, 6, and 8. |

### Wrong programs

The reviewer ran each wrong program in its model on proposed cases, and the containment test and the module cases include those cases.

| Wrong program | Cases that detect it |
|---|---|
| GMST with 67310.54841 in `W`; `T` from `d − 51544`; `s` left out of `W` or `T`; the sign of `T³` flipped; `s` at its midpoint only; the angle negated | The random dates and the interval widths of the containment test |
| No reduction modulo 2π, or `n + 1` | The range test of `gmst` and the test's range check |
| No limit on `d` | `d = 2³²` with status 1 |
| A sign of `R3` or of polar motion, `xp` and `yp` exchanged, a wrong unit, polar motion omitted or applied before `R3` | The random TEME cases with polar motion up to 0.5″ |
| The polar-motion rotations in the other order | `xp = yp = 10″` at (7000, 0, 0) km, where the difference is 1.6·10⁻⁵ km against a width below 10⁻⁸ km |
| `f` in place of `e²`, `z` without `1 − e²`, the sine and cosine of the longitude exchanged | Every geodetic case and SOFA's `gd2gc` point |
| The far-side triple | Every geodetic case, by the oracle's longitude and height |
| The interval quotient as the widening | (42.75, 0, 5) km |
| No widening; the residual at the midpoint only | The boxes of positive width |
| The slope bound `p` in place of `p − a e²` | The box (6378 to 6379, 0 to 1, 0 to 1) km |
| `atan(y/x)` for the longitude; `π + 2 arctan` in the second formula | (−7000, 0, 10) km |
| The first longitude formula only | The boxes across the negative x-axis |
| The latitude not negated, or the signed `z` in the height, below the equator | (1, 0, −42.845) km and the southern polar box |
| The test of `D` with 42.70 in place of 42.84 | (1, 0, 42.80) km with status 3 |
| The equation in `u` always | (10⁻⁶, 0, 6356) km |
| No Newton steps | The width bound of the geodetic results |
| ΔAT taken where `dᵢ < d`, or one entry early | The first day of an entry and the random dates |
| A day length of 86400 always; a leap second at the start of the day; `s = L` accepted | (57753, 86400.5), (57754, 86400), and (57753, 86401) |
| A negative leap second ignored; `L(d)` with wraparound | The tables (60000, 50000, 30, 51000, 29) and (60000, 50000, 100000, 51000, 0) |
| TT without 32.184; −ΔAT; −δ | Every accepted time case |
| `d < E` in place of `d + 1 < E`; `d + 1` with wraparound | `d = 61583` and `d = 2⁶⁴ − 1` with status 2 |
| Repeated dates, `E` equal to the last date, or values of `2³²` accepted | Malformed tables with status 1 |
| `s = −0` rejected | `s = −0` with status 0 |

No case detects these classes:

- The decimal constants of GMST as binary64 points: the width of `W` exceeds their rounding errors at every input, so only the program text and the theorem over the real constants exclude them.
- TT with the binary64 value of 32.184: the outward step at 32 exceeds the rounding error of 32.184, so the result stays sound.
- The latitude from `atan` without the two outward steps: the widening exceeds the rounding error of the library's `atan`, and a model's `atan` is more accurate than the library's guarantee.
- `≥` in place of `>` in the tests of `D`: the lower end comes from a downward step and never equals zero.
