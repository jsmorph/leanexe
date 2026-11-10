import Library.Numerics.Float64.Trig.Program
import Library.Numerics.Float64.Pow.Program
import Library.Numerics.Float64.Atan.Program
import LeanExe.Dialect.RepeatWhile

/-!
The near-Earth SGP4 propagator in binary64.  `initWith` computes the constants of an element set,
and `propagateWith` computes the position and the velocity at a time from the epoch.  The
arithmetic follows the code of Vallado, Crawford, Hujsak, and Kelso (AIAA 2006-6753) with the
WGS-72 constants, without its reductions of angles modulo `2π`.  `requirements.md` maps each
definition to that code.
-/

namespace Demos.Sgp4

open Library.Numerics.Float64

/-- The double nearest to `π`. -/
abbrev pi : Float := Float.ofBits 0x400921FB54442D18

/-- The Earth's radius in km. -/
abbrev radius : Float := 6378.135

/-- The square root of the gravitational parameter in Earth radii and minutes. -/
abbrev xke : Float := 60.0 / Float.sqrt (radius * radius * radius / 398600.8)

abbrev j2 : Float := 0.001082616

abbrev j3oj2 : Float := -0.00000253881 / j2

abbrev j4 : Float := -0.00000165597

abbrev x2o3 : Float := 2.0 / 3.0

/-- The status of a set of constants or of a state: 0 for a result, 1, 2, 4, and 6 for the error
of that number in the reference code, 8 for an element set of the deep-space path, and 9 for an
element set outside `0 < n`, `0 ≤ e < 1`, or with a value that is not finite. -/
abbrev statusDeep : UInt64 := 8

abbrev statusInvalid : UInt64 := 9

/-- The constants of an element set: the elements in radians and radians per minute, and the
coefficients that the propagation uses. -/
structure Consts where
  status : UInt64
  isimp : UInt64
  no : Float
  ecco : Float
  inclo : Float
  nodeo : Float
  argpo : Float
  mo : Float
  bstar : Float
  sinio : Float
  cosio : Float
  con41 : Float
  x1mth2 : Float
  x7thm1 : Float
  mdot : Float
  argpdot : Float
  nodedot : Float
  nodecf : Float
  cc1 : Float
  cc4 : Float
  cc5 : Float
  t2cof : Float
  omgcof : Float
  eta : Float
  xmcof : Float
  delmo : Float
  sinmao : Float
  d2 : Float
  d3 : Float
  d4 : Float
  t3cof : Float
  t4cof : Float
  t5cof : Float
  aycof : Float
  xlcof : Float
  deriving Inhabited

/-- A position in km and a velocity in km/s in the TEME frame. -/
structure State where
  status : UInt64
  x : Float
  y : Float
  z : Float
  vx : Float
  vy : Float
  vz : Float
  deriving Inhabited

def isFinite (x : Float) : Bool := x - x == 0.0

/-- The constants with only a status. -/
def failed (status : UInt64) : Consts :=
  { status := status, isimp := 0, no := 0.0, ecco := 0.0, inclo := 0.0, nodeo := 0.0,
    argpo := 0.0, mo := 0.0, bstar := 0.0, sinio := 0.0, cosio := 0.0, con41 := 0.0,
    x1mth2 := 0.0, x7thm1 := 0.0, mdot := 0.0, argpdot := 0.0, nodedot := 0.0, nodecf := 0.0,
    cc1 := 0.0, cc4 := 0.0, cc5 := 0.0, t2cof := 0.0, omgcof := 0.0, eta := 0.0, xmcof := 0.0,
    delmo := 0.0, sinmao := 0.0, d2 := 0.0, d3 := 0.0, d4 := 0.0, t3cof := 0.0, t4cof := 0.0,
    t5cof := 0.0, aycof := 0.0, xlcof := 0.0 }

/-- The constants of the element set with mean motion `noKozai` in radians per minute, the
eccentricity `ecco`, the angles in radians, and the drag term `bstar`: `initl` and the near-Earth
part of `sgp4init`. -/
def initCore (inv half logTab expTab : Array UInt64)
    (noKozai ecco inclo nodeo argpo mo bstar : Float) : Consts :=
  let eccsq := ecco * ecco
  let omeosq := 1.0 - eccsq
  let rteosq := Float.sqrt omeosq
  let cosio := Trig.cosWith inv half inclo
  let cosio2 := cosio * cosio
  let ak := Pow.powWith logTab expTab (xke / noKozai) x2o3
  let d1 := 0.75 * j2 * (3.0 * cosio2 - 1.0) / (rteosq * omeosq)
  let del0 := d1 / (ak * ak)
  let adel := ak * (1.0 - del0 * del0 - del0 * (1.0 / 3.0 + 134.0 * del0 * del0 / 81.0))
  let del1 := d1 / (adel * adel)
  let no := noKozai / (1.0 + del1)
  if 2.0 * pi / no ≥ 225.0 then failed statusDeep
  else
    let ao := Pow.powWith logTab expTab (xke / no) x2o3
    let sinio := Trig.sinWith inv half inclo
    let po := ao * omeosq
    let con42 := 1.0 - 5.0 * cosio2
    let con41 := -con42 - cosio2 - cosio2
    let posq := po * po
    let rp := ao * (1.0 - ecco)
    let ss := 78.0 / radius + 1.0
    let qzms2ttemp := (120.0 - 78.0) / radius
    let qzms2t := qzms2ttemp * qzms2ttemp * qzms2ttemp * qzms2ttemp
    let isimp : UInt64 := if rp < 220.0 / radius + 1.0 then 1 else 0
    let perige := (rp - 1.0) * radius
    let sKm := if perige < 98.0 then 20.0 else perige - 78.0
    let qzms24temp := (120.0 - sKm) / radius
    let sfour := if perige < 156.0 then sKm / radius + 1.0 else ss
    let qzms24 :=
      if perige < 156.0 then qzms24temp * qzms24temp * qzms24temp * qzms24temp else qzms2t
    let pinvsq := 1.0 / posq
    let tsi := 1.0 / (ao - sfour)
    let eta := ao * ecco * tsi
    let etasq := eta * eta
    let eeta := ecco * eta
    let psisq := Float.abs (1.0 - etasq)
    let coef := qzms24 * Pow.powWith logTab expTab tsi 4.0
    let coef1 := coef / Pow.powWith logTab expTab psisq 3.5
    let cc2 := coef1 * no * (ao * (1.0 + 1.5 * etasq + eeta * (4.0 + etasq)) +
      0.375 * j2 * tsi / psisq * con41 * (8.0 + 3.0 * etasq * (8.0 + etasq)))
    let cc1 := bstar * cc2
    let cc3 := if ecco > 1.0e-4 then -2.0 * coef * tsi * j3oj2 * no * sinio / ecco else 0.0
    let x1mth2 := 1.0 - cosio2
    let cc4 := 2.0 * no * coef1 * ao * omeosq *
      (eta * (2.0 + 0.5 * etasq) + ecco * (0.5 + 2.0 * etasq) - j2 * tsi / (ao * psisq) *
        (-3.0 * con41 * (1.0 - 2.0 * eeta + etasq * (1.5 - 0.5 * eeta)) +
          0.75 * x1mth2 * (2.0 * etasq - eeta * (1.0 + etasq)) *
            Trig.cosWith inv half (2.0 * argpo)))
    let cc5 := 2.0 * coef1 * ao * omeosq * (1.0 + 2.75 * (etasq + eeta) + eeta * etasq)
    let cosio4 := cosio2 * cosio2
    let temp1 := 1.5 * j2 * pinvsq * no
    let temp2 := 0.5 * temp1 * j2 * pinvsq
    let temp3 := -0.46875 * j4 * pinvsq * pinvsq * no
    let mdot := no + 0.5 * temp1 * rteosq * con41 +
      0.0625 * temp2 * rteosq * (13.0 - 78.0 * cosio2 + 137.0 * cosio4)
    let argpdot := -0.5 * temp1 * con42 +
      0.0625 * temp2 * (7.0 - 114.0 * cosio2 + 395.0 * cosio4) +
      temp3 * (3.0 - 36.0 * cosio2 + 49.0 * cosio4)
    let xhdot1 := -temp1 * cosio
    let nodedot := xhdot1 +
      (0.5 * temp2 * (4.0 - 19.0 * cosio2) + 2.0 * temp3 * (3.0 - 7.0 * cosio2)) * cosio
    let omgcof := bstar * cc3 * Trig.cosWith inv half argpo
    let xmcof := if ecco > 1.0e-4 then -x2o3 * coef * bstar / eeta else 0.0
    let nodecf := 3.5 * omeosq * xhdot1 * cc1
    let t2cof := 1.5 * cc1
    let xlcof :=
      if Float.abs (cosio + 1.0) > 1.5e-12 then
        -0.25 * j3oj2 * sinio * (3.0 + 5.0 * cosio) / (1.0 + cosio)
      else -0.25 * j3oj2 * sinio * (3.0 + 5.0 * cosio) / 1.5e-12
    let aycof := -0.5 * j3oj2 * sinio
    let delmotemp := 1.0 + eta * Trig.cosWith inv half mo
    let delmo := delmotemp * delmotemp * delmotemp
    let sinmao := Trig.sinWith inv half mo
    let x7thm1 := 7.0 * cosio2 - 1.0
    let cc1sq := cc1 * cc1
    let d2 := 4.0 * ao * tsi * cc1sq
    let temp := d2 * tsi * cc1 / 3.0
    let d3 := (17.0 * ao + sfour) * temp
    let d4 := 0.5 * temp * ao * tsi * (221.0 * ao + 31.0 * sfour) * cc1
    let t3cof := d2 + 2.0 * cc1sq
    let t4cof := 0.25 * (3.0 * d3 + cc1 * (12.0 * d2 + 10.0 * cc1sq))
    let t5cof := 0.2 * (3.0 * d4 + 12.0 * cc1 * d3 + 6.0 * d2 * d2 +
      15.0 * cc1sq * (2.0 * d2 + cc1sq))
    let full := isimp == 0
    { status := 0, isimp := isimp, no := no, ecco := ecco, inclo := inclo, nodeo := nodeo,
      argpo := argpo, mo := mo, bstar := bstar, sinio := sinio, cosio := cosio, con41 := con41,
      x1mth2 := x1mth2, x7thm1 := x7thm1, mdot := mdot, argpdot := argpdot, nodedot := nodedot,
      nodecf := nodecf, cc1 := cc1, cc4 := cc4, cc5 := cc5, t2cof := t2cof, omgcof := omgcof,
      eta := eta, xmcof := xmcof, delmo := delmo, sinmao := sinmao,
      d2 := if full then d2 else 0.0, d3 := if full then d3 else 0.0,
      d4 := if full then d4 else 0.0, t3cof := if full then t3cof else 0.0,
      t4cof := if full then t4cof else 0.0, t5cof := if full then t5cof else 0.0,
      aycof := aycof, xlcof := xlcof }

/-- The constants of the element set with mean motion `n` in revolutions per day, the
eccentricity `e`, the inclination, the right ascension of the node, the argument of perigee, and
the mean anomaly in degrees, and the drag term `bstar`. -/
def initWith (inv half logTab expTab : Array UInt64) (n e incl node argp m bstar : Float) :
    Consts :=
  if isFinite n && isFinite e && isFinite incl && isFinite node && isFinite argp && isFinite m &&
      isFinite bstar && n > 0.0 && e ≥ 0.0 && e < 1.0 then
    let deg := pi / 180.0
    initCore inv half logTab expTab (n / (1440.0 / (2.0 * pi))) e (incl * deg) (node * deg)
      (argp * deg) (m * deg) bstar
  else failed statusInvalid

/-- A state with only a status. -/
def stopped (status : UInt64) : State := ⟨status, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0⟩

/-- One step of the reference code's iteration for Kepler's equation, on the eccentric anomaly,
the last correction, and the sine and the cosine of the anomaly before the correction. -/
def keplerStep (inv half : Array UInt64) (axnl aynl u : Float)
    (s : Float × Float × Float × Float) : Float × Float × Float × Float :=
  let eo1 := s.1
  let sineo1 := Trig.sinWith inv half eo1
  let coseo1 := Trig.cosWith inv half eo1
  let slope := 1.0 - coseo1 * axnl - sineo1 * aynl
  let tem5 := (u - aynl * coseo1 + axnl * sineo1 - eo1) / slope
  let tem5 :=
    if Float.abs tem5 ≥ 0.95 then (if tem5 > 0.0 then 0.95 else -0.95) else tem5
  (eo1 + tem5, tem5, sineo1, coseo1)

/-- The state at `t` minutes from the epoch: the near-Earth part of `sgp4`. -/
def propagateWith (inv half logTab expTab : Array UInt64) (c : Consts) (t : Float) : State :=
  if c.status != 0 then stopped c.status
  else if isFinite t then
    let xmdf := c.mo + c.mdot * t
    let argpdf := c.argpo + c.argpdot * t
    let nodedf := c.nodeo + c.nodedot * t
    let t2 := t * t
    let nodem := nodedf + c.nodecf * t2
    let tempa0 := 1.0 - c.cc1 * t
    let tempe0 := c.bstar * c.cc4 * t
    let templ0 := c.t2cof * t2
    let full := c.isimp == 0
    let delomg := c.omgcof * t
    let delmtemp := 1.0 + c.eta * Trig.cosWith inv half xmdf
    let delm := c.xmcof * (delmtemp * delmtemp * delmtemp - c.delmo)
    let temp := delomg + delm
    let mm := if full then xmdf + temp else xmdf
    let argpm := if full then argpdf - temp else argpdf
    let t3 := t2 * t
    let t4 := t3 * t
    let tempa := if full then tempa0 - c.d2 * t2 - c.d3 * t3 - c.d4 * t4 else tempa0
    let tempe :=
      if full then tempe0 + c.bstar * c.cc5 * (Trig.sinWith inv half mm - c.sinmao) else tempe0
    let templ :=
      if full then templ0 + c.t3cof * t3 + t4 * (c.t4cof + t * c.t5cof) else templ0
    let nm := c.no
    if nm ≤ 0.0 then stopped 2
    else
      let am := Pow.powWith logTab expTab (xke / nm) x2o3 * tempa * tempa
      let nm := xke / Pow.powWith logTab expTab am 1.5
      let em := c.ecco - tempe
      if em ≥ 1.0 || em < -0.001 then stopped 1
      else
        let em := if em < 1.0e-6 then 1.0e-6 else em
        let mm := mm + c.no * templ
        let axnl := em * Trig.cosWith inv half argpm
        let temp := 1.0 / (am * (1.0 - em * em))
        let aynl := em * Trig.sinWith inv half argpm + temp * c.aycof
        let u := mm + argpm + temp * c.xlcof * axnl
        let k := LeanExe.repeatWhile 10 (u, 9999.9, 0.0, 0.0)
          (fun s => Float.abs s.2.1 ≥ 1.0e-12) (keplerStep inv half axnl aynl u)
        let sineo1 := k.2.2.1
        let coseo1 := k.2.2.2
        let ecose := axnl * coseo1 + aynl * sineo1
        let esine := axnl * sineo1 - aynl * coseo1
        let el2 := axnl * axnl + aynl * aynl
        let pl := am * (1.0 - el2)
        if pl < 0.0 then stopped 4
        else
          let rl := am * (1.0 - ecose)
          let rdotl := Float.sqrt am * esine / rl
          let rvdotl := Float.sqrt pl / rl
          let betal := Float.sqrt (1.0 - el2)
          let temp := esine / (1.0 + betal)
          let sinu := am / rl * (sineo1 - aynl - axnl * temp)
          let cosu := am / rl * (coseo1 - axnl + aynl * temp)
          let su := Atan.atan2 sinu cosu
          let sin2u := (cosu + cosu) * sinu
          let cos2u := 1.0 - 2.0 * sinu * sinu
          let temp := 1.0 / pl
          let temp1 := 0.5 * j2 * temp
          let temp2 := temp1 * temp
          let mrt := rl * (1.0 - 1.5 * temp2 * betal * c.con41) + 0.5 * temp1 * c.x1mth2 * cos2u
          let su := su - 0.25 * temp2 * c.x7thm1 * sin2u
          let xnode := nodem + 1.5 * temp2 * c.cosio * sin2u
          let xinc := c.inclo + 1.5 * temp2 * c.cosio * c.sinio * cos2u
          let mvt := rdotl - nm * temp1 * c.x1mth2 * sin2u / xke
          let rvdot := rvdotl + nm * temp1 * (c.x1mth2 * cos2u + 1.5 * c.con41) / xke
          let sinsu := Trig.sinWith inv half su
          let cossu := Trig.cosWith inv half su
          let snod := Trig.sinWith inv half xnode
          let cnod := Trig.cosWith inv half xnode
          let sini := Trig.sinWith inv half xinc
          let cosi := Trig.cosWith inv half xinc
          let xmx := -snod * cosi
          let xmy := cnod * cosi
          let ux := xmx * sinsu + cnod * cossu
          let uy := xmy * sinsu + snod * cossu
          let uz := sini * sinsu
          let vx := xmx * cossu - cnod * sinsu
          let vy := xmy * cossu - snod * sinsu
          let vz := sini * cossu
          let mr := mrt * radius
          let vkmpersec := radius * xke / 60.0
          { status := if mrt < 1.0 then 6 else 0
            x := mr * ux, y := mr * uy, z := mr * uz
            vx := (mvt * ux + rvdot * vx) * vkmpersec
            vy := (mvt * uy + rvdot * vy) * vkmpersec
            vz := (mvt * uz + rvdot * vz) * vkmpersec }
  else stopped statusInvalid

/-- The state of an element set at `t` minutes from its epoch. -/
def sgp4With (inv half logTab expTab : Array UInt64) (n e incl node argp m bstar t : Float) :
    State :=
  propagateWith inv half logTab expTab (initWith inv half logTab expTab n e incl node argp m bstar)
    t

def init (n e incl node argp m bstar : Float) : Consts :=
  initWith Trig.invPi Trig.halfPi Pow.powLogTable Exp.expTable n e incl node argp m bstar

def propagate (c : Consts) (t : Float) : State :=
  propagateWith Trig.invPi Trig.halfPi Pow.powLogTable Exp.expTable c t

def sgp4 (n e incl node argp m bstar t : Float) : State :=
  sgp4With Trig.invPi Trig.halfPi Pow.powLogTable Exp.expTable n e incl node argp m bstar t

end Demos.Sgp4
