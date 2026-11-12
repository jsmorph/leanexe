import Library.Numerics.Interval.Enclose
import Demos.Geolocation.Rotation

/-!
The measurement model in interval arithmetic.  Each `enclosure_def` declares a real function, its
interval function, whose name ends in `I`, and the theorem `encloses` that the interval function's
result contains the real function's result when each interval argument contains the real
argument.  The squares are written `|d| * |d|`, whose interval has a lower end of at least zero.
The theorems at the end equate the real functions with the model.
-/

open Real

namespace Demos.Geolocation

/-- The distance from `(sx, sy, sz)` to `(x, y, z)`. -/
enclosure_def dist (sx sy sz x y z) :=
  let dx := sx - x
  let dy := sy - y
  let dz := sz - z
  √(|dx| * |dx| + |dy| * |dy| + |dz| * |dz|)

/-- The range rate of a receiver at `(sx, sy, sz)` with velocity `(ux, uy, uz)`. -/
enclosure_def rate (sx sy sz ux uy uz x y z) :=
  let dx := sx - x
  let dy := sy - y
  let dz := sz - z
  (dx * ux + dy * uy + dz * uz) / √(|dx| * |dx| + |dy| * |dy| + |dz| * |dz|)

/-- The residual of a time difference: the model less the measured value `v`. -/
enclosure_def tdoaRes (ax ay az qx qy qz x y z v) :=
  (dist ax ay az x y z - dist qx qy qz x y z) / 299792.458 - v

/-- The residual of a frequency difference for the carrier frequency `f`: the model less the
measured value `v`. -/
enclosure_def fdoaRes (f ax ay az au av aw qx qy qz qu qv qw x y z v) :=
  f * (rate qx qy qz qu qv qw x y z - rate ax ay az au av aw x y z) / 299792.458 - v

/-- The rate of the sidereal angle at the day `d` and the seconds `s` of UT1, in rad/s. -/
enclosure_def spin (d s) :=
  let t := (d - 51544.5 + s / 86400) / 36525
  π / 43200 * (1 + (8640184.812866 + t * (2 * 0.093104 - 3 * 6.2e-6 * t)) / 3155760000)

/-- The Earth-fixed velocity of the TEME position `(x, y, z)` with velocity `(u, v, q)` at the
angle `ψ` turning at the rate `w`: the frames demo's rotation of `(u + w y, v − w x, q)`. -/
enclosure_def earthVel (ψ w xp yp x y z u v q) : 3 :=
  Frames.toEarth ψ xp yp (u + w * y) (v - w * x) q

theorem spin_eq (d s : ℝ) : spin d s = Model.spin d s := rfl

/-- The interval form of the velocity is `earthVelocity`, and it depends on the angle only modulo
`2π`. -/
theorem earthVel_eq (ψ w xp yp : ℝ) (r v : Model.V3) (k : ℤ) :
    earthVel (ψ - 2 * π * k) w xp yp r.1 r.2.1 r.2.2 v.1 v.2.1 v.2.2 =
      Model.earthVelocity ψ w xp yp r v := by
  show Frames.toEarth (ψ - 2 * π * k) xp yp (v.1 + w * r.2.1) (v.2.1 - w * r.1) v.2.2 = _
  rw [Frames.toEarth_periodic, Frames.toEarth_eq]
  rfl

theorem sq_abs (d : ℝ) : |d| * |d| = d ^ 2 := by rw [abs_mul_abs_self, pow_two]

theorem dist_eq (sx sy sz x y z : ℝ) :
    dist sx sy sz x y z = Model.range (sx, sy, sz) (x, y, z) := by
  simp only [dist, Model.range, sq_abs]

theorem rate_eq (sx sy sz ux uy uz x y z : ℝ) :
    rate sx sy sz ux uy uz x y z = Model.rangeRate (sx, sy, sz) (ux, uy, uz) (x, y, z) := by
  simp only [rate, Model.rangeRate, Model.range, sq_abs]

theorem tdoaRes_eq (a q x : Model.V3) (v : ℝ) :
    tdoaRes a.1 a.2.1 a.2.2 q.1 q.2.1 q.2.2 x.1 x.2.1 x.2.2 v = Model.tdoa a q x - v := by
  simp only [tdoaRes, dist_eq, Model.tdoa, Model.c, Prod.mk.eta]

theorem fdoaRes_eq (f : ℝ) (a au q qu x : Model.V3) (v : ℝ) :
    fdoaRes f a.1 a.2.1 a.2.2 au.1 au.2.1 au.2.2 q.1 q.2.1 q.2.2 qu.1 qu.2.1 qu.2.2 x.1 x.2.1
      x.2.2 v = Model.fdoa f a au q qu x - v := by
  simp only [fdoaRes, rate_eq, Model.fdoa, Model.c, Prod.mk.eta]
  ring

end Demos.Geolocation
