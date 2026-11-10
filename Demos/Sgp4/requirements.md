# SGP4 requirements

These requirements define the near-Earth SGP4 propagator of this directory.  The source is the code of Vallado, Crawford, Hujsak, and Kelso, "Revisiting Spacetrack Report #3" (AIAA 2006-6753), in the version that [python-sgp4](https://github.com/brandon-rhodes/python-sgp4) distributes as `extension/SGP4.cpp` and transliterates in `sgp4/propagation.py`.  Each table names the function of that code that holds the equations.  [The review](review.md) records each difference from that code.

## Inputs and outputs

An element set holds the mean motion `n` in revolutions per day, the eccentricity `e`, the inclination `i`, the right ascension of the ascending node `Ω`, the argument of perigee `ω`, and the mean anomaly `M` in degrees, and the drag term `B*` in inverse Earth radii.  The time `t` is in minutes from the epoch of the element set.  The result holds a status, the position in km, and the velocity in km/s, in the TEME frame of the reference code.

| Status | Meaning |
|---|---|
| 0 | The position and the velocity are those of the model. |
| 1 | The mean eccentricity at `t` is at least 1 or below −0.001. |
| 2 | The mean motion is not positive. |
| 4 | The semilatus rectum is negative. |
| 6 | The radius is below one Earth radius.  The position and the velocity are still those of the model. |
| 8 | The period is 225 minutes or more, the deep-space path, which this version does not compute. |
| 9 | A value is not finite, `n ≤ 0`, `e < 0`, or `1 ≤ e`. |

## Constants

The constants are those of WGS-72 in the function `getgravconst`.

| Name | Value |
|---|---|
| `μ` | 398600.8 km³/s² |
| `R` | 6378.135 km |
| `xke` | `60 / √(R³ / μ)` |
| `J2` | 0.001082616 |
| `J3` | −0.00000253881 |
| `J4` | −0.00000165597 |
| `j3oj2` | `J3 / J2` |

## Conversion of units

The function `twoline2rv` converts the element set: `no_kozai = n / (1440 / 2π)` in radians per minute, and each angle is its value in degrees times `π / 180`.  The names `inclo`, `nodeo`, `argpo`, and `mo` denote the converted angles, and `ecco` and `bstar` denote `e` and `B*`.

## Constants of an element set

The function `initl` recovers the mean motion and the semimajor axis.

| Name | Definition |
|---|---|
| `eccsq`, `omeosq`, `rteosq` | `ecco²`, `1 − eccsq`, `√omeosq` |
| `cosio`, `sinio`, `cosio2` | `cos inclo`, `sin inclo`, `cosio²` |
| `ak` | `(xke / no_kozai)^(2/3)` |
| `d1` | `0.75 J2 (3 cosio2 − 1) / (rteosq omeosq)` |
| `del₀` | `d1 / ak²` |
| `adel` | `ak (1 − del₀² − del₀ (1/3 + 134 del₀² / 81))` |
| `del` | `d1 / adel²` |
| `no` | `no_kozai / (1 + del)` |
| `ao` | `(xke / no)^(2/3)` |
| `po`, `posq` | `ao omeosq`, `po²` |
| `con42`, `con41` | `1 − 5 cosio2`, `−con42 − 2 cosio2` |
| `rp` | `ao (1 − ecco)` |

The element set takes the deep-space path when `2π / no ≥ 225`.  The function `sgp4init` computes the remaining constants.

| Name | Definition |
|---|---|
| `isimp` | `rp < 220 / R + 1` |
| `perige` | `(rp − 1) R` |
| `sfour` | `78 / R + 1` when `156 ≤ perige`, `(perige − 78) / R + 1` when `98 ≤ perige < 156`, and `20 / R + 1` when `perige < 98` |
| `qzms24` | `((120 − 78) / R)⁴` when `156 ≤ perige`, `((120 − (perige − 78)) / R)⁴` when `98 ≤ perige < 156`, and `((120 − 20) / R)⁴` when `perige < 98` |
| `pinvsq`, `tsi` | `1 / posq`, `1 / (ao − sfour)` |
| `eta`, `etasq`, `eeta` | `ao ecco tsi`, `eta²`, `ecco eta` |
| `psisq` | `\|1 − etasq\|` |
| `coef`, `coef1` | `qzms24 tsi⁴`, `coef / psisq^3.5` |
| `cc2` | `coef1 no (ao (1 + 1.5 etasq + eeta (4 + etasq)) + 0.375 J2 tsi / psisq con41 (8 + 3 etasq (8 + etasq)))` |
| `cc1` | `bstar cc2` |
| `cc3` | `−2 coef tsi j3oj2 no sinio / ecco` when `ecco > 10⁻⁴`, and 0 otherwise |
| `x1mth2`, `x7thm1` | `1 − cosio2`, `7 cosio2 − 1` |
| `cc4` | `2 no coef1 ao omeosq (eta (2 + 0.5 etasq) + ecco (0.5 + 2 etasq) − J2 tsi / (ao psisq) (−3 con41 (1 − 2 eeta + etasq (1.5 − 0.5 eeta)) + 0.75 x1mth2 (2 etasq − eeta (1 + etasq)) cos (2 argpo)))` |
| `cc5` | `2 coef1 ao omeosq (1 + 2.75 (etasq + eeta) + eeta etasq)` |
| `cosio4` | `cosio2²` |
| `temp1`, `temp2`, `temp3` | `1.5 J2 pinvsq no`, `0.5 temp1 J2 pinvsq`, `−0.46875 J4 pinvsq² no` |
| `mdot` | `no + 0.5 temp1 rteosq con41 + 0.0625 temp2 rteosq (13 − 78 cosio2 + 137 cosio4)` |
| `argpdot` | `−0.5 temp1 con42 + 0.0625 temp2 (7 − 114 cosio2 + 395 cosio4) + temp3 (3 − 36 cosio2 + 49 cosio4)` |
| `xhdot1` | `−temp1 cosio` |
| `nodedot` | `xhdot1 + (0.5 temp2 (4 − 19 cosio2) + 2 temp3 (3 − 7 cosio2)) cosio` |
| `omgcof` | `bstar cc3 cos argpo` |
| `xmcof` | `−(2/3) coef bstar / eeta` when `ecco > 10⁻⁴`, and 0 otherwise |
| `nodecf`, `t2cof` | `3.5 omeosq xhdot1 cc1`, `1.5 cc1` |
| `xlcof` | `−0.25 j3oj2 sinio (3 + 5 cosio) / (1 + cosio)` when `\|cosio + 1\| > 1.5·10⁻¹²`, and the same numerator over `1.5·10⁻¹²` otherwise |
| `aycof` | `−0.5 j3oj2 sinio` |
| `delmo`, `sinmao` | `(1 + eta cos mo)³`, `sin mo` |
| `cc1sq`, `d2` | `cc1²`, `4 ao tsi cc1sq` |
| `temp`, `d3` | `d2 tsi cc1 / 3`, `(17 ao + sfour) temp` |
| `d4` | `0.5 temp ao tsi (221 ao + 31 sfour) cc1` |
| `t3cof` | `d2 + 2 cc1sq` |
| `t4cof` | `0.25 (3 d3 + cc1 (12 d2 + 10 cc1sq))` |
| `t5cof` | `0.2 (3 d4 + 12 cc1 d3 + 6 d2² + 15 cc1sq (2 d2 + cc1sq))` |

The propagation uses `d2`, `d3`, `d4`, `t3cof`, `t4cof`, and `t5cof` only when `isimp` is false.

## Propagation

The function `sgp4` computes the state at `t`.  The secular terms come first.

| Name | Definition |
|---|---|
| `xmdf`, `argpdf`, `nodedf` | `mo + mdot t`, `argpo + argpdot t`, `nodeo + nodedot t` |
| `nodem` | `nodedf + nodecf t²` |
| `delomg`, `delm` | `omgcof t`, `xmcof ((1 + eta cos xmdf)³ − delmo)` |
| `mm₀`, `argpm` | `xmdf + delomg + delm` and `argpdf − delomg − delm` when `isimp` is false, and `xmdf` and `argpdf` otherwise |
| `tempa` | `1 − cc1 t − d2 t² − d3 t³ − d4 t⁴` when `isimp` is false, and `1 − cc1 t` otherwise |
| `tempe` | `bstar cc4 t + bstar cc5 (sin mm₀ − sinmao)` when `isimp` is false, and `bstar cc4 t` otherwise |
| `templ` | `t2cof t² + t3cof t³ + t⁴ (t4cof + t t5cof)` when `isimp` is false, and `t2cof t²` otherwise |
| `am` | `(xke / no)^(2/3) tempa²` |
| `nm` | `xke / am^1.5` |
| `em₀` | `ecco − tempe` |
| `em` | `max em₀ 10⁻⁶` |
| `mm` | `mm₀ + no templ` |

Status 2 holds when `no ≤ 0`, and status 1 when `em₀ ≥ 1` or `em₀ < −0.001`.  The long-period terms and Kepler's equation follow.

| Name | Definition |
|---|---|
| `axnl` | `em cos argpm` |
| `temp` | `1 / (am (1 − em²))` |
| `aynl` | `em sin argpm + temp aycof` |
| `u` | `mm + argpm + temp xlcof axnl` |
| `E` | The root of `E + aynl cos E − axnl sin E = u` |
| `ecose`, `esine` | `axnl cos E + aynl sin E`, `axnl sin E − aynl cos E` |
| `el2`, `pl` | `axnl² + aynl²`, `am (1 − el2)` |

Status 4 holds when `pl < 0`.  The short-period terms and the vectors follow.

| Name | Definition |
|---|---|
| `rl` | `am (1 − ecose)` |
| `rdotl`, `rvdotl` | `√am esine / rl`, `√pl / rl` |
| `betal` | `√(1 − el2)` |
| `temp` | `esine / (1 + betal)` |
| `sinu`, `cosu` | `am / rl (sin E − aynl − axnl temp)`, `am / rl (cos E − axnl + aynl temp)` |
| `su₀` | The argument of the point `(cosu, sinu)` |
| `sin2u`, `cos2u` | `2 cosu sinu`, `1 − 2 sinu²` |
| `temp1`, `temp2` | `0.5 J2 / pl`, `temp1 / pl` |
| `mrt` | `rl (1 − 1.5 temp2 betal con41) + 0.5 temp1 x1mth2 cos2u` |
| `su` | `su₀ − 0.25 temp2 x7thm1 sin2u` |
| `xnode` | `nodem + 1.5 temp2 cosio sin2u` |
| `xinc` | `inclo + 1.5 temp2 cosio sinio cos2u` |
| `mvt` | `rdotl − nm temp1 x1mth2 sin2u / xke` |
| `rvdot` | `rvdotl + nm temp1 (x1mth2 cos2u + 1.5 con41) / xke` |
| `xmx`, `xmy` | `−sin xnode cos xinc`, `cos xnode cos xinc` |
| `(ux, uy, uz)` | `(xmx sin su + cos xnode cos su, xmy sin su + sin xnode cos su, sin xinc sin su)` |
| `(vx, vy, vz)` | `(xmx cos su − cos xnode sin su, xmy cos su − sin xnode sin su, sin xinc cos su)` |
| Position | `mrt R (ux, uy, uz)` |
| Velocity | `(mvt (ux, uy, uz) + rvdot (vx, vy, vz)) R xke / 60` |

Status 6 holds when `mrt < 1`.

## Programs

[The binary64 program](Program.lean) evaluates these definitions in binary64 with the library's `sin`, `cos`, `pow`, and `atan2`.  It finds `E` with the reference code's iteration: Newton's method from `u`, with each correction limited to 0.95 in magnitude, until a correction is below `10⁻¹²` in magnitude or 10 corrections are done, and it takes the sine and the cosine of the iterate before the last correction.

## Tests

`tests/sgp4/run.sh` compares the binary64 program with the reference states of the verification file of the Vallado code for its near-Earth element sets.  Each position must lie within `10⁻⁸` km of the reference, which is printed to `10⁻⁸` km, and each velocity within `10⁻⁹` km/s.  The verification file holds no state for the last times of three element sets, and the program's status at each of those times must differ from 0.
