import Library.Numerics.Interval.Enclose
import Demos.Screening.KeplerBox
import Demos.Screening.Model

/-!
The parts of the two-body model that the program evaluates on intervals.  Each `enclosure_def`
declares a real function, the interval function `fI` that the program runs, and the theorem
`f.encloses`.  The theorems at the end equate each real function with the definitions of
`Model.lean`, so that the enclosures concern the model.
-/

open Real Demos.Sgp4

namespace Demos.Screening.Spec

/-- The mean motion in radians per minute, `√(1 - e²)`, the unit vectors `P` and `Q`, the bound
`a n / (1 - e)` of the speed in km per minute, and the perigee and apogee radii in km, for `μ` in
km³/s², `a` in km, and the angles in degrees. -/
enclosure_def orbit (mu a e incl node argp) :=
  let deg := π / 180
  let ci := cos (incl * deg)
  let si := sin (incl * deg)
  let co := cos (node * deg)
  let so := sin (node * deg)
  let cw := cos (argp * deg)
  let sw := sin (argp * deg)
  let n := 60 * √(mu / (a * a * a))
  (n, √(1 - e * e), cw * co - sw * so * ci, cw * so + sw * co * ci, sw * si,
    -sw * co - cw * so * ci, -sw * so + cw * co * ci, cw * si, a * n / (1 - e), a * (1 - e),
    a * (1 + e))

/-- The point of the path at the eccentric anomaly `E`. -/
enclosure_def pathPoint (a e beta px py pz qx qy qz E) :=
  let p := a * (cos E - e)
  let q := a * beta * sin E
  (p * px + q * qx, p * py + q * qy, p * pz + q * qz)

/-- The eccentric anomaly at `t` minutes for the mean motion `n`, the mean anomaly `m0` in
degrees at the epoch, and the epoch. -/
enclosure_def anomaly (e n m0 epoch t) := kepler e (m0 * (π / 180) + n * (t - epoch))

/-- The squared distance of two points. -/
enclosure_def distSq (x1 y1 z1 x2 y2 z2) :=
  let dx := x1 - x2
  let dy := y1 - y2
  let dz := z1 - z2
  |dx| * |dx| + |dy| * |dy| + |dz| * |dz|

/-! ### The real functions are the model's -/

theorem orbit_eq (mu : ℝ) (o : Orbit) :
    orbit mu o.a o.e o.incl o.node o.argp =
      (o.motion mu, o.beta, o.toPerigee.1, o.toPerigee.2.1, o.toPerigee.2.2, o.ahead.1,
        o.ahead.2.1, o.ahead.2.2, o.speed mu, o.a * (1 - o.e), o.a * (1 + o.e)) := rfl

theorem pathPoint_eq (o : Orbit) (E : ℝ) :
    pathPoint o.a o.e o.beta o.toPerigee.1 o.toPerigee.2.1 o.toPerigee.2.2 o.ahead.1 o.ahead.2.1
      o.ahead.2.2 E = o.path E := rfl

theorem anomaly_eq (mu : ℝ) (o : Orbit) (t : ℝ) :
    anomaly o.e (o.motion mu) o.m0 o.epoch t = o.anomaly mu t := rfl

theorem distSq_eq (p q : ℝ × ℝ × ℝ) :
    distSq p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 = dist3 p q ^ 2 := by
  rw [dist3_sq]
  simp only [distSq, abs_mul_abs_self]
  ring

end Demos.Screening.Spec
