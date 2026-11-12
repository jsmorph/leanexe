import Demos.Frames.Enclose
import LeanExe.Dialect.Loop

/-!
The programs of `requirements.md`.  `gmst` encloses the sidereal angle of a day and an interval of
seconds of UT1, less a whole number of turns, and `temeToEcef` rotates a box of TEME positions into
the Earth-fixed frame.  `toCartesian` encloses the Earth-fixed positions of a box of geodetic
coordinates, and `toGeodetic` the geodetic coordinates of a box of Earth-fixed positions.  Each
validates its arguments, evaluates the interval functions of `Enclose.lean`, and reports a status,
as `Soundness.lean` states.  The interval functions take the
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

/-- A status and the intervals of the latitude, the longitude, and the height. -/
structure Coords where
  status : UInt64
  lat : Interval
  lon : Interval
  h : Interval
  deriving Inhabited

/-- A status without intervals. -/
def noCoords (status : UInt64) : Coords := ⟨status, rejected, rejected, rejected⟩

/-- `a e²` and `1 − e²` of WGS 84, rounded to binary64, for the Newton steps. -/
abbrev ae2 : Float := 42.69767270717997
abbrev m84 : Float := 0.9933056200098587

/-- Six Newton steps on `k(u) = p u − z − a e² u/√(1 + (1 − e²) u²)` from `z/((1 − e²) p)`. -/
def newtonA (p z : Float) : Float :=
  LeanExe.loop 6 (z / (m84 * p)) fun _ u =>
    let q := 1.0 + m84 * (u * u)
    let r := q.sqrt
    u - (p * u - z - ae2 * u / r) / (p - ae2 / (q * r))

/-- Six Newton steps on `ℓ(v) = z v + a e² v/√(v² + 1 − e²) − p` from `(1 − e²) p/z`. -/
def newtonB (p z : Float) : Float :=
  LeanExe.loop 6 (m84 * p / z) fun _ v =>
    let q := v * v + m84
    let r := q.sqrt
    v - (z * v + ae2 * v / r - p) / (z + ae2 * m84 / (q * r))

/-- The float `e` widened by the quotient of the magnitude of the residual `r` and the slope
bound `s`, accepted when `s` lies above zero. -/
def widen (e : Float) (r s : Interval) : Interval :=
  let bound := div (abs r) s
  if bound.status == 0 then
    if 0 < s.lo then add (point e) (make (-bound.hi) bound.hi) else rejected
  else rejected

/-- The latitude and the height by the equation in `u = tan φ`. -/
def regimeA (inv half : Array UInt64) (p z : Interval) : Coords :=
  let s := slopeAI inv half inv half p
  if s.status == 0 then
    if 0 < s.lo then
      let e := newtonA (mid p) (mid z)
      let u := widen e (residualAI inv half inv half p z (point e)) s
      let c := coordsAI inv half inv half p z u
      if c.1.status == 0 && c.2.status == 0 then ⟨0, c.1, rejected, c.2⟩ else noCoords 2
    else noCoords 3
  else noCoords 2

/-- The latitude and the height by the equation in `v = cot φ`, for `z` on one side of 0. -/
def regimeB (inv half : Array UInt64) (p z : Interval) : Coords :=
  let below : Bool := mid z < 0
  let w := if below then neg z else z
  let s := slopeBI inv half inv half w
  if s.status == 0 then
    if 0 < s.lo then
      let e := newtonB (mid p) (mid w)
      let v := widen e (residualBI inv half inv half p w (point e)) w
      let c := coordsBI inv half inv half p w v
      if c.1.status == 0 && c.2.status == 0 then
        ⟨0, if below then neg c.1 else c.1, rejected, c.2⟩
      else noCoords 2
    else noCoords 3
  else noCoords 2

/-- The longitude of the box `x`, `y` with the distance `p` from the polar axis: `2 arctan(y/(p + x))`
when the midpoint of `x` is at least 0, and `π − 2 arctan(y/(p − x))` otherwise, accepted when the
interval of the divisor lies above 0. -/
def longitude (inv half : Array UInt64) (x y p : Interval) : Interval :=
  if 0 ≤ mid x then
    let q := add p x
    if q.status == 0 && 0 < q.lo then lonAI inv half inv half y q else rejected
  else
    let q := sub p x
    if q.status == 0 && 0 < q.lo then lonBI inv half inv half y q else rejected

def toGeodeticWith (inv half : Array UInt64) (xlo xhi ylo yhi zlo zhi : Float) : Coords :=
  let x := make xlo xhi
  let y := make ylo yhi
  let z := make zlo zhi
  if x.status == 0 && y.status == 0 && z.status == 0 then
    let p := axisI x y
    if p.status == 0 then
      if 0 < p.lo then
        let g := if mid (abs z) ≤ mid p then regimeA inv half p z else regimeB inv half p z
        if g.status == 0 then
          let lon := longitude inv half x y p
          if lon.status == 0 && (-4 : Int64).toFloat ≤ lon.lo && lon.hi ≤ (7 : Int64).toFloat then
            ⟨0, g.lat, lon, g.h⟩
          else noCoords 2
        else g
      else noCoords 3
    else noCoords 2
  else noCoords 1

def toCartesianWith (inv half : Array UInt64) (latlo lathi lonlo lonhi hlo hhi : Float) : Vec :=
  let lat := make latlo lathi
  let lon := make lonlo lonhi
  let h := make hlo hhi
  if lat.status == 0 && lon.status == 0 && h.status == 0 then
    let r := cartesianI inv half inv half lat lon h
    if r.1.status == 0 && r.2.1.status == 0 && r.2.2.status == 0 then ⟨0, r.1, r.2.1, r.2.2⟩
    else noVec 2
  else noVec 1

/-- The sidereal angle of the day `d` and the seconds `[lo, hi]` of UT1. -/
def gmst (d : UInt64) (lo hi : Float) : Angle := gmstWith Trig.invPi Trig.halfPi d lo hi

/-- The Earth-fixed position of a box of TEME positions at the day `d` and the seconds `s` of
UT1, with the polar motion `xp` and `yp` in arcseconds. -/
def temeToEcef (d : UInt64) (slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi : Float) : Vec :=
  temeToEcefWith Trig.invPi Trig.halfPi d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi

/-- The geodetic coordinates of a box of Earth-fixed positions in km. -/
def toGeodetic (xlo xhi ylo yhi zlo zhi : Float) : Coords :=
  toGeodeticWith Trig.invPi Trig.halfPi xlo xhi ylo yhi zlo zhi

/-- The Earth-fixed positions in km of a box of latitudes and longitudes in radians and heights
in km. -/
def toCartesian (latlo lathi lonlo lonhi hlo hhi : Float) : Vec :=
  toCartesianWith Trig.invPi Trig.halfPi latlo lathi lonlo lonhi hlo hhi

end Demos.Frames
