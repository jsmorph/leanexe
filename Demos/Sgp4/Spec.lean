import Library.Numerics.Interval.Enclose
import Demos.Sgp4.KeplerBox

/-!
The near-Earth SGP4 model over the real numbers, with an interval program for each part.

Each `enclosure_def` declares a real function, which is the specification of that part of
`requirements.md`, the interval function `fI`, and the theorem `f.encloses`.  `constants`
computes the constants of an element set, and `state` computes the quantities that decide the
status, the position, and the velocity at a time.  The parameters `radius`, `xke`, `j2`, `j3oj2`,
and `j4` are the Earth's radius and the gravity constants, which `Model.lean` sets to the WGS-72
values.
-/

open Real

namespace Demos.Sgp4.Spec

/-! ### Units and constants -/

/-- The mean motion in radians per minute and the four angles in radians. -/
enclosure_def convert (n incl node argp m) :=
  let deg := π / 180
  (n / (1440 / (2 * π)), incl * deg, node * deg, argp * deg, m * deg)

/-- The square root of the gravitational parameter in Earth radii and minutes. -/
enclosure_def xkeOf (radius mu) := 60 / √(radius * radius * radius / mu)

/-- The period in minutes of the mean motion `no`. -/
enclosure_def period (no) := 2 * π / no

/-! ### Constants of an element set -/

/-- The mean motion `no` with `cosio`, `cosio2`, `omeosq`, and `rteosq`. -/
enclosure_def unkozai (xke j2 noKozai ecco inclo) :=
  let eccsq := ecco * ecco
  let omeosq := 1 - eccsq
  let rteosq := √omeosq
  let cosio := cos inclo
  let cosio2 := cosio * cosio
  let ak := (xke / noKozai) ^ (2 / 3 : ℝ)
  let d1 := 0.75 * j2 * (3 * cosio2 - 1) / (rteosq * omeosq)
  let del0 := d1 / (ak * ak)
  let adel := ak * (1 - del0 * del0 - del0 * (1 / 3 + 134 * del0 * del0 / 81))
  let del := d1 / (adel * adel)
  (noKozai / (1 + del), cosio, cosio2, omeosq, rteosq)

/-- `ao`, `sinio`, `con41`, `con42`, `pinvsq`, `rp`, `x1mth2`, and `x7thm1`. -/
enclosure_def geometry (xke no ecco inclo cosio2 omeosq) :=
  let ao := (xke / no) ^ (2 / 3 : ℝ)
  let po := ao * omeosq
  let con42 := 1 - 5 * cosio2
  (ao, sin inclo, -con42 - cosio2 - cosio2, con42, 1 / (po * po), ao * (1 - ecco), 1 - cosio2,
    7 * cosio2 - 1)

/-- `sfour`, `qzms24`, `tsi`, `eta`, `etasq`, `eeta`, and `psisq`. -/
enclosure_def atmosphere (radius rp ao ecco) :=
  let perige := (rp - 1) * radius
  let sKm := if perige < 98 then 20 else perige - 78
  let sfour := if perige < 156 then sKm / radius + 1 else 78 / radius + 1
  let q := (120 - sKm) / radius
  let q0 := (120 - 78) / radius
  let qzms24 := if perige < 156 then q * q * q * q else q0 * q0 * q0 * q0
  let tsi := 1 / (ao - sfour)
  let eta := ao * ecco * tsi
  let etasq := eta * eta
  (sfour, qzms24, tsi, eta, etasq, ecco * eta, |1 - etasq|)

/-- `coef`, `coef1`, and `cc1`. -/
enclosure_def dragCoef (j2 bstar no ao con41 tsi etasq eeta psisq qzms24) :=
  let coef := qzms24 * (tsi * tsi * tsi * tsi)
  let coef1 := coef / psisq ^ (7 / 2 : ℝ)
  let cc2 := coef1 * no * (ao * (1 + 1.5 * etasq + eeta * (4 + etasq)) +
    0.375 * j2 * tsi / psisq * con41 * (8 + 3 * etasq * (8 + etasq)))
  (coef, coef1, bstar * cc2)

/-- The part of `cc4` in the inner parentheses. -/
enclosure_def dragInner (con41 x1mth2 argpo etasq eeta) :=
  -3 * con41 * (1 - 2 * eeta + etasq * (1.5 - 0.5 * eeta)) +
    0.75 * x1mth2 * (2 * etasq - eeta * (1 + etasq)) * cos (2 * argpo)

/-- `cc4`. -/
enclosure_def dragC4 (j2 no ao ecco omeosq tsi eta etasq psisq coef1 inner) :=
  2 * no * coef1 * ao * omeosq *
    (eta * (2 + 0.5 * etasq) + ecco * (0.5 + 2 * etasq) - j2 * tsi / (ao * psisq) * inner)

/-- `cc5`. -/
enclosure_def dragC5 (ao omeosq etasq eeta coef1) :=
  2 * coef1 * ao * omeosq * (1 + 2.75 * (etasq + eeta) + eeta * etasq)

/-- `temp1`, `temp2`, `temp3`, `cosio4`, and `mdot`. -/
enclosure_def ratesMean (j2 j4 no pinvsq rteosq con41 cosio2) :=
  let cosio4 := cosio2 * cosio2
  let temp1 := 1.5 * j2 * pinvsq * no
  let temp2 := 0.5 * temp1 * j2 * pinvsq
  let temp3 := -0.46875 * j4 * pinvsq * pinvsq * no
  (temp1, temp2, temp3, cosio4, no + 0.5 * temp1 * rteosq * con41 +
    0.0625 * temp2 * rteosq * (13 - 78 * cosio2 + 137 * cosio4))

/-- `argpdot`, `nodedot`, and `xhdot1`. -/
enclosure_def ratesAngles (temp1 temp2 temp3 con42 cosio cosio2 cosio4) :=
  let argpdot := -0.5 * temp1 * con42 + 0.0625 * temp2 * (7 - 114 * cosio2 + 395 * cosio4) +
    temp3 * (3 - 36 * cosio2 + 49 * cosio4)
  let xhdot1 := -temp1 * cosio
  (argpdot, xhdot1 + (0.5 * temp2 * (4 - 19 * cosio2) + 2 * temp3 * (3 - 7 * cosio2)) * cosio,
    xhdot1)

/-- `omgcof`, `xmcof`, `xlcof`, and `aycof`.  `low` is positive for a perigee below 220 km. -/
enclosure_def coupling (j3oj2 bstar no ecco sinio cosio argpo coef tsi eeta low) :=
  let cc3 := if ecco > 1.0e-4 then -2 * coef * tsi * j3oj2 * no * sinio / ecco else 0
  let omgcof := if 0 < low then 0 else bstar * cc3 * cos argpo
  let xmcof :=
    if 0 < low then 0 else if ecco > 1.0e-4 then -(2 / 3) * coef * bstar / eeta else 0
  let xlcof :=
    if |cosio + 1| > 1.5e-12 then -0.25 * j3oj2 * sinio * (3 + 5 * cosio) / (1 + cosio)
    else -0.25 * j3oj2 * sinio * (3 + 5 * cosio) / 1.5e-12
  (omgcof, xmcof, xlcof, -0.5 * j3oj2 * sinio)

/-- `nodecf`, `t2cof`, `delmo`, and `sinmao`. -/
enclosure_def epochTerms (omeosq xhdot1 cc1 eta mo) :=
  let d := 1 + eta * cos mo
  (3.5 * omeosq * xhdot1 * cc1, 1.5 * cc1, d * d * d, sin mo)

/-- `cc1sq`, `d2`, `d3`, and `d4`. -/
enclosure_def higherD (ao tsi cc1 sfour) :=
  let cc1sq := cc1 * cc1
  let d2 := 4 * ao * tsi * cc1sq
  let temp := d2 * tsi * cc1 / 3
  (cc1sq, d2, (17 * ao + sfour) * temp, 0.5 * temp * ao * tsi * (221 * ao + 31 * sfour) * cc1)

/-- `t3cof`, `t4cof`, and `t5cof`. -/
enclosure_def higherT (cc1 cc1sq d2 d3 d4) :=
  (d2 + 2 * cc1sq, 0.25 * (3 * d3 + cc1 * (12 * d2 + 10 * cc1sq)),
    0.2 * (3 * d4 + 12 * cc1 * d3 + 6 * d2 * d2 + 15 * cc1sq * (2 * d2 + cc1sq)))

/-- The constants of an element set in radians and radians per minute.  The terms that the
propagation omits for a perigee below 220 km are zero for such an element set. -/
enclosure_def constants (radius xke j2 j3oj2 j4 noKozai ecco inclo argpo mo bstar) :=
  let (no, cosio, cosio2, omeosq, rteosq) := unkozai xke j2 noKozai ecco inclo
  let (ao, sinio, con41, con42, pinvsq, rp, x1mth2, x7thm1) :=
    geometry xke no ecco inclo cosio2 omeosq
  let low := 220 / radius + 1 - rp
  let (sfour, qzms24, tsi, eta, etasq, eeta, psisq) := atmosphere radius rp ao ecco
  let (coef, coef1, cc1) := dragCoef j2 bstar no ao con41 tsi etasq eeta psisq qzms24
  let inner := dragInner con41 x1mth2 argpo etasq eeta
  let cc4 := dragC4 j2 no ao ecco omeosq tsi eta etasq psisq coef1 inner
  let cc5 := dragC5 ao omeosq etasq eeta coef1
  let (temp1, temp2, temp3, cosio4, mdot) := ratesMean j2 j4 no pinvsq rteosq con41 cosio2
  let (argpdot, nodedot, xhdot1) := ratesAngles temp1 temp2 temp3 con42 cosio cosio2 cosio4
  let (omgcof, xmcof, xlcof, aycof) :=
    coupling j3oj2 bstar no ecco sinio cosio argpo coef tsi eeta low
  let (nodecf, t2cof, delmo, sinmao) := epochTerms omeosq xhdot1 cc1 eta mo
  let (cc1sq, d2, d3, d4) := higherD ao tsi cc1 sfour
  let (t3cof, t4cof, t5cof) := higherT cc1 cc1sq d2 d3 d4
  (no, sinio, cosio, con41, x1mth2, x7thm1, mdot, argpdot, nodedot, nodecf, cc1, cc4,
    if 0 < low then 0 else cc5, t2cof, omgcof, eta, xmcof, delmo, sinmao,
    if 0 < low then 0 else d2, if 0 < low then 0 else d3, if 0 < low then 0 else d4,
    if 0 < low then 0 else t3cof, if 0 < low then 0 else t4cof, if 0 < low then 0 else t5cof,
    aycof, xlcof)

/-! ### Propagation -/

/-- `mm` before the drag term, `argpm`, and `nodem`. -/
enclosure_def secular (t nodeo argpo mo mdot argpdot nodedot nodecf omgcof xmcof eta delmo) :=
  let xmdf := mo + mdot * t
  let d := 1 + eta * cos xmdf
  let temp := omgcof * t + xmcof * (d * d * d - delmo)
  (xmdf + temp, argpo + argpdot * t - temp, nodeo + nodedot * t + nodecf * (t * t))

/-- `tempa`, `tempe`, and `templ`. -/
enclosure_def drag (t bstar cc1 cc4 cc5 d2 d3 d4 t2cof t3cof t4cof t5cof mm0 sinmao) :=
  let t2 := t * t
  let t3 := t2 * t
  let t4 := t3 * t
  (1 - cc1 * t - d2 * t2 - d3 * t3 - d4 * t4,
    bstar * cc4 * t + bstar * cc5 * (sin mm0 - sinmao),
    t2cof * t2 + t3cof * t3 + t4 * (t4cof + t * t5cof))

/-- `am`, `nm`, the mean eccentricity before and after its lower limit, and `mm`. -/
enclosure_def mean (xke no ecco tempa tempe templ mm0) :=
  let am := (xke / no) ^ (2 / 3 : ℝ) * tempa * tempa
  let em0 := ecco - tempe
  (am, xke / am ^ (3 / 2 : ℝ), em0, max em0 1.0e-6, mm0 + no * templ)

/-- `axnl`, `aynl`, and `u`. -/
enclosure_def longPeriod (am em argpm mm aycof xlcof) :=
  let axnl := em * cos argpm
  let temp := 1 / (am * (1 - em * em))
  (axnl, em * sin argpm + temp * aycof, mm + argpm + temp * xlcof * axnl)

/-- `esine`, `pl`, `rl`, `betal`, `sinu`, and `cosu`, from the root `e` of Kepler's equation. -/
enclosure_def anomaly (am axnl aynl e) :=
  let sineo1 := sin e
  let coseo1 := cos e
  let ecose := axnl * coseo1 + aynl * sineo1
  let esine := axnl * sineo1 - aynl * coseo1
  let el2 := axnl * axnl + aynl * aynl
  let rl := am * (1 - ecose)
  let betal := √(1 - el2)
  let temp := esine / (1 + betal)
  (esine, am * (1 - el2), rl, betal, am / rl * (sineo1 - aynl - axnl * temp),
    am / rl * (coseo1 - axnl + aynl * temp))

/-- `mrt`, the correction of the argument of latitude, `sin2u`, `cos2u`, `temp1`, and `temp2`. -/
enclosure_def shortRadius (j2 pl rl betal sinu cosu con41 x1mth2 x7thm1) :=
  let sin2u := (cosu + cosu) * sinu
  let cos2u := 1 - 2 * sinu * sinu
  let temp := 1 / pl
  let temp1 := 0.5 * j2 * temp
  let temp2 := temp1 * temp
  (rl * (1 - 1.5 * temp2 * betal * con41) + 0.5 * temp1 * x1mth2 * cos2u,
    0.25 * temp2 * x7thm1 * sin2u, sin2u, cos2u, temp1, temp2)

/-- `xnode`, `xinc`, `mvt`, and `rvdot`. -/
enclosure_def shortAngles (xke am nm esine pl rl sin2u cos2u temp1 temp2 con41 x1mth2 cosio
    sinio inclo nodem) :=
  (nodem + 1.5 * temp2 * cosio * sin2u, inclo + 1.5 * temp2 * cosio * sinio * cos2u,
    √am * esine / rl - nm * temp1 * x1mth2 * sin2u / xke,
    √pl / rl + nm * temp1 * (x1mth2 * cos2u + 1.5 * con41) / xke)

/-- The unit vectors of the position and of the transverse direction.  The sine and the cosine
of the argument of latitude `su - delta` come from `sinu`, `cosu`, and the angle `delta`. -/
enclosure_def orientation (sinu cosu delta xnode xinc) :=
  let sinsu := sinu * cos delta - cosu * sin delta
  let cossu := cosu * cos delta + sinu * sin delta
  let snod := sin xnode
  let cnod := cos xnode
  let sini := sin xinc
  let cosi := cos xinc
  let xmx := -snod * cosi
  let xmy := cnod * cosi
  (xmx * sinsu + cnod * cossu, xmy * sinsu + snod * cossu, sini * sinsu,
    xmx * cossu - cnod * sinsu, xmy * cossu - snod * sinsu, sini * cossu)

/-- The position in km and the velocity in km/s. -/
enclosure_def vectors (radius xke mrt mvt rvdot ux uy uz vx vy vz) :=
  let mr := mrt * radius
  let vkmpersec := radius * xke / 60
  (mr * ux, mr * uy, mr * uz, (mvt * ux + rvdot * vx) * vkmpersec,
    (mvt * uy + rvdot * vy) * vkmpersec, (mvt * uz + rvdot * vz) * vkmpersec)

/-- The mean eccentricity before its lower limit, the semilatus rectum, the radius in Earth
radii, the position, and the velocity at `t` minutes from the epoch. -/
enclosure_def state (radius xke j2 t ecco inclo nodeo argpo mo bstar no sinio cosio con41 x1mth2
    x7thm1 mdot argpdot nodedot nodecf cc1 cc4 cc5 t2cof omgcof eta xmcof delmo sinmao d2 d3 d4
    t3cof t4cof t5cof aycof xlcof) :=
  let (mm0, argpm, nodem) :=
    secular t nodeo argpo mo mdot argpdot nodedot nodecf omgcof xmcof eta delmo
  let (tempa, tempe, templ) :=
    drag t bstar cc1 cc4 cc5 d2 d3 d4 t2cof t3cof t4cof t5cof mm0 sinmao
  let (am, nm, em0, em, mm) := mean xke no ecco tempa tempe templ mm0
  let (axnl, aynl, u) := longPeriod am em argpm mm aycof xlcof
  let e := Kepler.root axnl aynl u
  let (esine, pl, rl, betal, sinu, cosu) := anomaly am axnl aynl e
  let (mrt, delta, sin2u, cos2u, temp1, temp2) :=
    shortRadius j2 pl rl betal sinu cosu con41 x1mth2 x7thm1
  let (xnode, xinc, mvt, rvdot) :=
    shortAngles xke am nm esine pl rl sin2u cos2u temp1 temp2 con41 x1mth2 cosio sinio inclo nodem
  let (ux, uy, uz, vx, vy, vz) := orientation sinu cosu delta xnode xinc
  let (x, y, z, xdot, ydot, zdot) := vectors radius xke mrt mvt rvdot ux uy uz vx vy vz
  (em0, pl, mrt, x, y, z, xdot, ydot, zdot)

/-! ### The whole computation -/

/-- The period in minutes, `no`, `xke`, the eccentricity, the angles in radians, the drag term,
and the constants of `constants` after `no`, for an element set in revolutions per day and
degrees. -/
enclosure_def elements (radius mu j2 j3oj2 j4 n ecco incl node argp m bstar) :=
  let (noKozai, inclo, nodeo, argpo, mo) := convert n incl node argp m
  let xke := xkeOf radius mu
  let (no, sinio, cosio, con41, x1mth2, x7thm1, mdot, argpdot, nodedot, nodecf, cc1, cc4, cc5, t2cof,
      omgcof, eta, xmcof, delmo, sinmao, d2, d3, d4, t3cof, t4cof, t5cof, aycof, xlcof) :=
    constants radius xke j2 j3oj2 j4 noKozai ecco inclo argpo mo bstar
  (period no, no, xke, ecco, inclo, nodeo, argpo, mo, bstar,
    sinio, cosio, con41, x1mth2, x7thm1, mdot, argpdot, nodedot, nodecf, cc1, cc4, cc5, t2cof,
    omgcof, eta, xmcof, delmo, sinmao, d2, d3, d4, t3cof, t4cof, t5cof, aycof, xlcof)

/-- The result of `state` for the tuple `c` of `elements`. -/
enclosure_def stateAt (radius j2 t) {c : 35} :=
  let (per, no, xke, ecco, inclo, nodeo, argpo, mo, bstar,
    sinio, cosio, con41, x1mth2, x7thm1, mdot, argpdot, nodedot, nodecf, cc1, cc4, cc5, t2cof,
    omgcof, eta, xmcof, delmo, sinmao, d2, d3, d4, t3cof, t4cof, t5cof, aycof, xlcof) := c
  let (em0, pl, mrt, x, y, z, xdot, ydot, zdot) :=
    state radius xke j2 t ecco inclo nodeo argpo mo bstar no
      sinio cosio con41 x1mth2 x7thm1 mdot argpdot nodedot nodecf cc1 cc4 cc5 t2cof omgcof eta
      xmcof delmo sinmao d2 d3 d4 t3cof t4cof t5cof aycof xlcof
  (em0, pl, mrt, x, y, z, xdot, ydot, zdot)

/-- `elements` with the WGS-72 constants. -/
enclosure_def wgs72 (n ecco incl node argp m bstar) : 35 :=
  elements 6378.135 398600.8 0.001082616 (-0.00000253881 / 0.001082616) (-0.00000165597) n ecco
    incl node argp m bstar

/-- `stateAt` with the WGS-72 constants. -/
enclosure_def wgs72State (t) {c : 35} : 9 := stateAt 6378.135 0.001082616 t c

end Demos.Sgp4.Spec
