import Demos.Frames.Enclose

/-!
The programs of `requirements.md`.  `gmst` encloses the sidereal angle of a day and an interval of
seconds of UT1, less a whole number of turns, and `temeToEcef` rotates a box of TEME positions into
the Earth-fixed frame.  Each validates its arguments, evaluates the interval functions of
`Enclose.lean`, and reports a status, as `Soundness.lean` states.  The interval functions take the
tables of `pow` as well as those of `sin` and `cos`, use no power, and receive the tables of `sin`
and `cos` in their place.
-/

namespace Demos.Frames

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- A status and an interval of an angle in radians. -/
structure Angle where
  status : UInt64
  lo : Float
  hi : Float
  deriving Inhabited

/-- A status and an interval for each of three coordinates. -/
structure Vec where
  status : UInt64
  x : Interval
  y : Interval
  z : Interval
  deriving Inhabited

/-- A status without intervals. -/
def noVec (status : UInt64) : Vec := ⟨status, rejected, rejected, rejected⟩

/-- The floor of `q`, from its truncation toward zero, for `q` within the range of `Int64`. -/
def floorOf (q : Float) : Int64 :=
  let n := q.toInt64
  if q < n.toFloat then n - 1 else n

/-- An interval of the sidereal angle of the day `d` and the seconds `s` of UT1, less the whole
turns of the floor of the midpoint of `W` over 86400. -/
def angleWith (inv half : Array UInt64) (d : UInt64) (s : Interval) : Interval :=
  let w := gmstSecondsI inv half inv half (ofInt d.toInt64) s
  if w.status == 0 then
    let n := floorOf (mid w / 86400.0)
    if -9007199254740992 ≤ n && n ≤ 9007199254740992 then turnsI inv half inv half w (ofInt n)
    else rejected
  else rejected

def gmstWith (inv half : Array UInt64) (d : UInt64) (lo hi : Float) : Angle :=
  let s := make lo hi
  if d < 4294967296 && s.status == 0 then
    let r := angleWith inv half d s
    if r.status == 0 && (-1 : Int64).toFloat ≤ r.lo && r.hi ≤ (7 : Int64).toFloat then
      ⟨0, r.lo, r.hi⟩
    else ⟨2, 0, 0⟩
  else ⟨1, 0, 0⟩

def temeToEcefWith (inv half : Array UInt64) (d : UInt64)
    (slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi : Float) : Vec :=
  let s := make slo shi
  let xp := make xplo xphi
  let yp := make yplo yphi
  let x := make xlo xhi
  let y := make ylo yhi
  let z := make zlo zhi
  if d < 4294967296 && s.status == 0 && xp.status == 0 && yp.status == 0 && x.status == 0 &&
      y.status == 0 && z.status == 0 then
    let r := toEarthI inv half inv half (angleWith inv half d s) xp yp x y z
    if r.1.status == 0 && r.2.1.status == 0 && r.2.2.status == 0 then ⟨0, r.1, r.2.1, r.2.2⟩
    else noVec 2
  else noVec 1

/-- The sidereal angle of the day `d` and the seconds `[lo, hi]` of UT1. -/
def gmst (d : UInt64) (lo hi : Float) : Angle := gmstWith Trig.invPi Trig.halfPi d lo hi

/-- The Earth-fixed position of a box of TEME positions at the day `d` and the seconds `s` of
UT1, with the polar motion `xp` and `yp` in arcseconds. -/
def temeToEcef (d : UInt64) (slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi : Float) : Vec :=
  temeToEcefWith Trig.invPi Trig.halfPi d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi

end Demos.Frames
