import Library.Numerics.Interval.Enclose
import Demos.Frames.Model

/-!
The formulas of `requirements.md` in interval arithmetic.  Each `enclosure_def` declares a real
function, its interval function, whose name ends in `I`, and the theorem `encloses` that the
interval function's result contains the real function's result when each interval argument
contains the real argument.  The theorems at the end equate the real functions with the model.
-/

open Real

namespace Demos.Frames

/-- The seconds `W(d, s)` of the sidereal time of the day `d` and the seconds `s` of UT1. -/
enclosure_def gmstSeconds (d s) :=
  let t := (d - 51544.5 + s / 86400) / 36525
  s + 24110.54841 + t * (8640184.812866 + t * (0.093104 - 6.2e-6 * t))

/-- The angle of `w - 86400 n` seconds of sidereal time. -/
enclosure_def turns (w n) := (w - 86400 * n) * (π / 43200)

/-- The rotation `R1(−yp) R2(−xp) R3(ψ)` of the position `(x, y, z)`, with `xp` and `yp` in
arcseconds. -/
enclosure_def toEarth (ψ xp yp x y z) :=
  let c := cos ψ
  let s := sin ψ
  let u := c * x + s * y
  let v := c * y - s * x
  let ax := xp * (π / 648000)
  let ay := yp * (π / 648000)
  let cx := cos ax
  let sx := sin ax
  let cy := cos ay
  let sy := sin ay
  let w := cx * z - sx * u
  (cx * u + sx * z, cy * v - sy * w, sy * v + cy * w)

/-- The sidereal angle is `2π (d − 51544)` plus the angle of `W(d, s)` seconds. -/
theorem gmst82_eq (d s : ℝ) :
    Model.gmst82 (Model.julian d s) = 2 * π * (d - 51544) + gmstSeconds d s * (π / 43200) := by
  simp only [Model.gmst82, Model.julian, gmstSeconds]
  ring

/-- The angle of `turns` is the sidereal angle less a whole number of turns. -/
theorem turns_eq (d s : ℝ) (n : ℤ) :
    turns (gmstSeconds d s) n = Model.gmst82 (Model.julian d s) - 2 * π * ((d - 51544) + n) := by
  rw [gmst82_eq]
  simp only [turns]
  ring

/-- `toEarth` is the rotation of the model. -/
theorem toEarth_eq (ψ xp yp x y z : ℝ) :
    toEarth ψ xp yp x y z = Model.earthFixed ψ xp yp (x, y, z) := by
  simp only [toEarth, Model.earthFixed, Model.rx, Model.ry, Model.rz, Model.arcsec, cos_neg,
    sin_neg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- The rotation depends on the angle only modulo `2π`. -/
theorem toEarth_periodic (ψ xp yp x y z : ℝ) (k : ℤ) :
    toEarth (ψ - 2 * π * k) xp yp x y z = toEarth ψ xp yp x y z := by
  have hc : cos (ψ - 2 * π * k) = cos ψ := by
    rw [show ψ - 2 * π * k = ψ - k * (2 * π) by ring]; exact cos_sub_int_mul_two_pi ψ k
  have hs : sin (ψ - 2 * π * k) = sin ψ := by
    rw [show ψ - 2 * π * k = ψ - k * (2 * π) by ring]; exact sin_sub_int_mul_two_pi ψ k
  simp only [toEarth, hc, hs]

end Demos.Frames
