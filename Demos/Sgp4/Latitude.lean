import Demos.Sgp4.Spec
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
The argument of latitude.  The reference code computes the angle `su = atan2 (sinu, cosu)`,
subtracts a correction `delta`, and takes the sine and the cosine of the difference.
`Spec.orientation` computes that sine and cosine from `sinu`, `cosu`, and `delta` without the
angle.  `anomaly_unit` states that `(cosu, sinu)` is a unit vector, and `sin_latitude` and
`cos_latitude` state that the two forms agree for a unit vector.
-/

namespace Demos.Sgp4

open Real

/-- The values `sinu` and `cosu` of `Spec.anomaly` are the sine and the cosine of one angle. -/
theorem anomaly_unit {am a b e : ℝ} (ham : am ≠ 0) (hel : a * a + b * b < 1) :
    (Spec.anomaly am a b e).2.2.2.2.1 ^ 2 + (Spec.anomaly am a b e).2.2.2.2.2 ^ 2 = 1 := by
  have hsc := sin_sq_add_cos_sq e
  have hβ : √(1 - (a * a + b * b)) ^ 2 = 1 - (a * a + b * b) := sq_sqrt (by linarith)
  have hβ0 : 0 ≤ √(1 - (a * a + b * b)) := sqrt_nonneg _
  have hc := Kepler.combination_le a b e
  have hlt : √(a ^ 2 + b ^ 2) < 1 := by
    have := sqrt_lt_sqrt (by positivity) (show a ^ 2 + b ^ 2 < 1 by nlinarith)
    rwa [sqrt_one] at this
  have hD : 1 - (a * cos e + b * sin e) ≠ 0 := by
    have := (abs_le.mp hc).2
    intro h
    linarith
  have h1 : (1 : ℝ) + √(1 - (a * a + b * b)) ≠ 0 := by linarith
  simp only [Spec.anomaly]
  set β := √(1 - (a * a + b * b)) with hβdef
  set T := (a * sin e - b * cos e) / (1 + β) with hTdef
  have hT : a * sin e - b * cos e = T * (1 + β) := by
    rw [hTdef]; field_simp
  have key : (sin e - b - a * T) ^ 2 + (cos e - a + b * T) ^ 2 =
      (1 - (a * cos e + b * sin e)) ^ 2 := by
    linear_combination (1 - (a * a + b * b)) * hsc +
      (a * sin e - b * cos e + T * (β - 1)) * hT + T ^ 2 * hβ
  have hq : am / (am * (1 - (a * cos e + b * sin e))) = 1 / (1 - (a * cos e + b * sin e)) := by
    field_simp
  rw [hq]
  field_simp
  linear_combination key

/-- The sine of the argument of the unit vector `(cosu, sinu)` less `delta`. -/
theorem sin_latitude {sinu cosu : ℝ} (h : sinu ^ 2 + cosu ^ 2 = 1) (delta : ℝ) :
    sin (Complex.arg (cosu + sinu * Complex.I) - delta) =
      sinu * cos delta - cosu * sin delta := by
  have hn : ‖(cosu : ℂ) + sinu * Complex.I‖ = 1 := by
    rw [Complex.norm_add_mul_I, add_comm, h, sqrt_one]
  have hz : (cosu : ℂ) + sinu * Complex.I ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rw [sin_sub, Complex.sin_arg, Complex.cos_arg hz, hn]
  simp

/-- The cosine of the argument of the unit vector `(cosu, sinu)` less `delta`. -/
theorem cos_latitude {sinu cosu : ℝ} (h : sinu ^ 2 + cosu ^ 2 = 1) (delta : ℝ) :
    cos (Complex.arg (cosu + sinu * Complex.I) - delta) =
      cosu * cos delta + sinu * sin delta := by
  have hn : ‖(cosu : ℂ) + sinu * Complex.I‖ = 1 := by
    rw [Complex.norm_add_mul_I, add_comm, h, sqrt_one]
  have hz : (cosu : ℂ) + sinu * Complex.I ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  rw [cos_sub, Complex.sin_arg, Complex.cos_arg hz, hn]
  simp

end Demos.Sgp4
