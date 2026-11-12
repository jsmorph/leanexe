import Library.Numerics.Interval.Enclose
import Demos.Screening.Spec
import Demos.Events.Model

/-!
The parts of the event model that the program evaluates on intervals.  Each `enclosure_def`
declares a real function, the interval function `fI` that the program runs, and the theorem
`f.encloses`.  The theorems at the end equate each real function with the definitions of
`Model.lean`, so that the enclosures concern the model.
-/

open Real

namespace Demos.Events.Spec

/-- The Sun's direction at `t` minutes for minute 0 at `d0` days from J2000.0. -/
enclosure_def sunDir (d0 t) :=
  let D := d0 + t / 1440
  let g := (357.529 + 0.98560028 * D) * (π / 180)
  let lam := (280.459 + 0.98564736 * D + 1.915 * sin g + 0.020 * sin (2 * g)) * (π / 180)
  let eps := (23.439 - 0.00000036 * D) * (π / 180)
  (cos lam, cos eps * sin lam, sin eps * sin lam)

/-- The cosine and sine of an angle in degrees. -/
enclosure_def angle (a) :=
  let x := a * (π / 180)
  (cos x, sin x)

/-- The length of a vector. -/
enclosure_def length (x y z) := √(|x| * |x| + |y| * |y| + |z| * |z|)

/-- The shadow's functions `r · s` and `|r × s| cos α + (r · s) sin α - R`. -/
enclosure_def shadowParts (rx ry rz sx sy sz ca sa R) :=
  let d := rx * sx + ry * sy + rz * sz
  let c1 := ry * sz - rz * sy
  let c2 := rz * sx - rx * sz
  let c3 := rx * sy - ry * sx
  (d, √(|c1| * |c1| + |c2| * |c2| + |c3| * |c3|) * ca + d * sa - R)

/-- The exclusion events' function `|b| cos β - v · s`. -/
enclosure_def vectorPart (nb cb vx vy vz sx sy sz) := nb * cb - (vx * sx + vy * sy + vz * sz)

/-- The vector with components `b` in the radial, along-track, and cross-track frame of the
position `r` on the orbit with the unit vectors `p` and `q`. -/
enclosure_def rswVec (rx ry rz px py pz qx qy qz b1 b2 b3) :=
  let wx := py * qz - pz * qy
  let wy := pz * qx - px * qz
  let wz := px * qy - py * qx
  let n := √(|rx| * |rx| + |ry| * |ry| + |rz| * |rz|)
  let ux := rx / n
  let uy := ry / n
  let uz := rz / n
  let sx := wy * uz - wz * uy
  let sy := wz * ux - wx * uz
  let sz := wx * uy - wy * ux
  (b1 * ux + b2 * sx + b3 * wx, b1 * uy + b2 * sy + b3 * wy, b1 * uz + b2 * sz + b3 * wz)

/-- The rate bounds: the shadow's two, the inertial vector's, and the rate of a vector in the
orbit's frame, from the speed bound, the apogee and perigee radii, the cosine and sine of the
angle, the length of `b`, and its first two components. -/
enclosure_def rates (speed apogee perigee ca sa nb b1 b2) :=
  let w := π / 180 * (0.98564736 + (1.915 + 2 * 0.020) * 0.98560028 * (π / 180) + 0.00000036) /
    1440
  let l := speed + apogee * w
  (l, (|ca| + |sa|) * l, nb * w, (|b1| + |b2|) * (speed / perigee) + nb * w)

/-- The shadow's second margin `(|cos α| + |sin α|) P`. -/
enclosure_def pad (ca sa p) := (|ca| + |sa|) * p

/-! ### The real functions are the model's -/

theorem sunDir_eq (d0 t : ℝ) : sunDir d0 t = sunAt d0 t := rfl

theorem angle_eq (a : ℝ) :
    angle a = (cos (Demos.Screening.rad a), sin (Demos.Screening.rad a)) := rfl

theorem abs_sq3 (x y z : ℝ) : |x| * |x| + |y| * |y| + |z| * |z| = x * x + y * y + z * z := by
  simp only [abs_mul_abs_self]

theorem length_eq (b : V3) : length b.1 b.2.1 b.2.2 = norm3 b := by
  unfold length norm3
  rw [abs_sq3]

theorem shadowParts_eq (r s : V3) (ca sa R : ℝ) :
    shadowParts r.1 r.2.1 r.2.2 s.1 s.2.1 s.2.2 ca sa R = (dot r s, shadowG2 ca sa R r s) := by
  unfold shadowParts shadowG2 norm3 cross dot
  simp only [abs_mul_abs_self]

theorem vectorPart_eq (nb cb : ℝ) (v s : V3) :
    vectorPart nb cb v.1 v.2.1 v.2.2 s.1 s.2.1 s.2.2 = vectorG nb cb v s := rfl

theorem rswVec_eq (mu : ℝ) (o : Demos.Screening.Orbit) (b : V3) (t : ℝ) :
    let r := o.position mu t
    rswVec r.1 r.2.1 r.2.2 o.toPerigee.1 o.toPerigee.2.1 o.toPerigee.2.2 o.ahead.1 o.ahead.2.1
      o.ahead.2.2 b.1 b.2.1 b.2.2 = rsw mu o b t := by
  intro r
  unfold rswVec rsw along radial normal unit3 add3 smul3 cross
  simp only [abs_mul_abs_self]
  rfl

end Demos.Events.Spec
