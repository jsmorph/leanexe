import Demos.Orbit.Gibbs
import Library.Numerics.Interval.Enclose

/-!
The interval program of Gibbs' method.  `gibbsCoords` states Gibbs' formula in coordinates with
the command `enclosure_def`, which also declares the interval function `gibbsCoordsI` and the
theorem `gibbsCoords.encloses`.  `gibbsBox` checks its inputs, rejects boxes whose triple product
`r1 · (r2 × r3)` the arithmetic shows to be nonzero, and returns the intervals of `gibbsCoordsI`.

| Status | Meaning |
|---|---|
| 0 | The intervals contain the velocity at `r2` of every orbit through the boxes in the order of the positions. |
| 1 | The triple product's interval lies above or below zero: no orbit passes through the boxes. |
| 2 | An interval operation rejected. |
| 3 | An input interval is not accepted or not finite, has `lo > hi`, or `μ`'s does not lie above zero. |
-/

namespace Demos.Orbit

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- `x²`. -/
def sqr (x : ℝ) : ℝ := x * x

set_option linter.unusedVariables false in
/-- The squares of the points of an interval. -/
def sqrI (trigInv trigHalf powLog powExp : Array UInt64) (a : Interval) : Interval := sq a

@[enclose] theorem sqr.encloses {powLog powExp : Array UInt64} {a : Interval} {x : ℝ}
    (h : Encloses a x) : Encloses (sqrI Trig.invPi Trig.halfPi powLog powExp a) (sqr x) :=
  encloses_sq h

/-- The length of `(x, y, z)`. -/
enclosure_def lengthOf (x y z) := √(sqr x + sqr y + sqr z)

/-- The cross product of `(ax, ay, az)` and `(bx, by', bz)`. -/
enclosure_def crossOf (ax ay az bx by' bz) :=
  (ay * bz - az * by', az * bx - ax * bz, ax * by' - ay * bx)

/-- `w1 a + w2 b + w3 c`. -/
enclosure_def weighted (w1 w2 w3 ax ay az bx by' bz cx cy cz) :=
  (w1 * ax + w2 * bx + w3 * cx, w1 * ay + w2 * by' + w3 * cy, w1 * az + w2 * bz + w3 * cz)

/-- Gibbs' formula in coordinates: `√(μ/(N · D)) (D × r2/n2 + S)`. -/
enclosure_def gibbsCoords (x1 y1 z1 x2 y2 z2 x3 y3 z3 mu) :=
  let n1 := lengthOf x1 y1 z1
  let n2 := lengthOf x2 y2 z2
  let n3 := lengthOf x3 y3 z3
  let (ax, ay, az) := crossOf x1 y1 z1 x2 y2 z2
  let (bx, by', bz) := crossOf x2 y2 z2 x3 y3 z3
  let (cx, cy, cz) := crossOf x3 y3 z3 x1 y1 z1
  let dx := ax + bx + cx
  let dy := ay + by' + cy
  let dz := az + bz + cz
  let (nx, ny, nz) := weighted n1 n2 n3 bx by' bz cx cy cz ax ay az
  let (sx, sy, sz) := weighted (n2 - n3) (n3 - n1) (n1 - n2) x1 y1 z1 x2 y2 z2 x3 y3 z3
  let f := √(mu / (nx * dx + ny * dy + nz * dz))
  let (ex, ey, ez) := crossOf dx dy dz x2 y2 z2
  (f * (ex / n2 + sx), f * (ey / n2 + sy), f * (ez / n2 + sz))

/-- The triple product `r1 · (r2 × r3)`. -/
enclosure_def triple (x1 y1 z1 x2 y2 z2 x3 y3 z3) :=
  x1 * (y2 * z3 - z2 * y3) + y1 * (z2 * x3 - x2 * z3) + z1 * (x2 * y3 - y2 * x3)

/-- A status and the intervals of the velocity at the middle position. -/
structure Velocity where
  status : UInt64
  vx : Interval
  vy : Interval
  vz : Interval
  deriving Inhabited

/-- A status without intervals. -/
def noVelocity (status : UInt64) : Velocity := ⟨status, rejected, rejected, rejected⟩

/-- The tables of `sin`, `cos`, and `pow`, which Gibbs' formula does not read. -/
def noTable : Array UInt64 := #[]

/-- An accepted interval with finite endpoints and `lo ≤ hi`. -/
def valid (a : Interval) : Bool := a.status == 0 && finite a.lo && finite a.hi && a.lo ≤ a.hi

/-- Gibbs' method on boxes of the three positions and an interval of `μ`. -/
def gibbsBox (x1 y1 z1 x2 y2 z2 x3 y3 z3 mu : Interval) : Velocity :=
  if valid x1 && valid y1 && valid z1 && valid x2 && valid y2 && valid z2 && valid x3 &&
      valid y3 && valid z3 && valid mu then
    if 0 < mu.lo then
      let t := tripleI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 x3 y3 z3
      if t.status = 0 ∧ (0 < t.lo ∨ t.hi < 0) then noVelocity 1
      else
        let v := gibbsCoordsI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 x3 y3 z3 mu
        if v.1.status == 0 && v.2.1.status == 0 && v.2.2.status == 0 then
          ⟨0, v.1, v.2.1, v.2.2⟩
        else noVelocity 2
    else noVelocity 3
  else noVelocity 3

/-- `gibbsBox` on the intervals between the given endpoints. -/
def gibbsBounds (x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi x3lo x3hi y3lo y3hi
    z3lo z3hi mulo muhi : Float) : Velocity :=
  gibbsBox (make x1lo x1hi) (make y1lo y1hi) (make z1lo z1hi) (make x2lo x2hi) (make y2lo y2hi)
    (make z2lo z2hi) (make x3lo x3hi) (make y3lo y3hi) (make z3lo z3hi) (make mulo muhi)

end Demos.Orbit
