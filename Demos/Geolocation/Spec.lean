import Library.Numerics.Interval.Enclose
import Demos.Geolocation.Model

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
