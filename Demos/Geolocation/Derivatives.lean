import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Demos.Geolocation.Rotation

/-!
The derivatives behind the TEME frame's model.  `gmst_hasDerivAt` (M3) states that `spin` is the
derivative of the sidereal angle with respect to the seconds of UT1, and `earthFixed_hasDerivAt`
(M2) that `earthVelocity` is the derivative of the Earth-fixed position of a TEME trajectory, with
the polar motion constant.
-/

open Real

namespace Demos.Geolocation.Model

/-- **M3.**  `spin` is the derivative of the sidereal angle with respect to the seconds of UT1. -/
theorem gmst_hasDerivAt (d s : ℝ) : HasDerivAt (theta d) (spin d s) s := by
  have ht : HasDerivAt (fun s => (d - 51544.5 + s / 86400) / 36525) (1 / 86400 / 36525) s :=
    HasDerivAt.div_const (HasDerivAt.const_add (d - 51544.5)
      (HasDerivAt.div_const (hasDerivAt_id s) 86400)) 36525
  have h2 := HasDerivAt.const_sub (0.093104 : ℝ) (HasDerivAt.const_mul (6.2e-6 : ℝ) ht)
  have h4 := HasDerivAt.const_add (8640184.812866 : ℝ) (HasDerivAt.fun_mul ht h2)
  have h6 := HasDerivAt.fun_add (HasDerivAt.add_const (24110.54841 : ℝ) (hasDerivAt_id s))
    (HasDerivAt.fun_mul ht h4)
  have h7 := HasDerivAt.const_add (2 * π * (d - 51544)) (HasDerivAt.mul_const h6 (π / 43200))
  have hf : theta d = fun s => 2 * π * (d - 51544) + (id s + 24110.54841 +
      (d - 51544.5 + s / 86400) / 36525 * (8640184.812866 + (d - 51544.5 + s / 86400) / 36525 *
        (0.093104 - 6.2e-6 * ((d - 51544.5 + s / 86400) / 36525)))) * (π / 43200) := by
    funext s
    simp only [theta, Frames.gmst82_eq, Frames.gmstSeconds, id]
  rw [hf]
  refine h7.congr_deriv ?_
  simp only [spin]
  ring

theorem hasDerivAt_rz {θ r₁ r₂ : ℝ → ℝ} {ω v₁ v₂ t : ℝ} (hθ : HasDerivAt θ ω t)
    (h1 : HasDerivAt r₁ v₁ t) (h2 : HasDerivAt r₂ v₂ t) :
    HasDerivAt (fun t => cos (θ t) * r₁ t + sin (θ t) * r₂ t)
        (cos (θ t) * (v₁ + ω * r₂ t) + sin (θ t) * (v₂ - ω * r₁ t)) t ∧
      HasDerivAt (fun t => -sin (θ t) * r₁ t + cos (θ t) * r₂ t)
        (-sin (θ t) * (v₁ + ω * r₂ t) + cos (θ t) * (v₂ - ω * r₁ t)) t := by
  have hc := HasDerivAt.cos hθ
  have hs := HasDerivAt.sin hθ
  refine ⟨(HasDerivAt.fun_add (HasDerivAt.fun_mul hc h1) (HasDerivAt.fun_mul hs h2)).congr_deriv
    (by ring), (HasDerivAt.fun_add (HasDerivAt.fun_mul (HasDerivAt.fun_neg hs) h1)
      (HasDerivAt.fun_mul hc h2)).congr_deriv (by ring)⟩

/-- **M2.**  For a TEME trajectory whose coordinates `r₁`, `r₂`, `r₃` have the derivatives `v` at
`t`, and a sidereal angle `θ` with the derivative `ω` at `t`, the derivative at `t` of each
coordinate of the Earth-fixed position `E(θ) r` is that coordinate of
`earthVelocity (θ t) ω xp yp (r t) v`. -/
theorem earthFixed_hasDerivAt {θ r₁ r₂ r₃ : ℝ → ℝ} {ω t xp yp : ℝ} {v : V3}
    (hθ : HasDerivAt θ ω t) (h1 : HasDerivAt r₁ v.1 t) (h2 : HasDerivAt r₂ v.2.1 t)
    (h3 : HasDerivAt r₃ v.2.2 t) :
    HasDerivAt (fun t => (Frames.Model.earthFixed (θ t) xp yp (r₁ t, r₂ t, r₃ t)).1)
        (earthVelocity (θ t) ω xp yp (r₁ t, r₂ t, r₃ t) v).1 t ∧
      HasDerivAt (fun t => (Frames.Model.earthFixed (θ t) xp yp (r₁ t, r₂ t, r₃ t)).2.1)
        (earthVelocity (θ t) ω xp yp (r₁ t, r₂ t, r₃ t) v).2.1 t ∧
      HasDerivAt (fun t => (Frames.Model.earthFixed (θ t) xp yp (r₁ t, r₂ t, r₃ t)).2.2)
        (earthVelocity (θ t) ω xp yp (r₁ t, r₂ t, r₃ t) v).2.2 t := by
  obtain ⟨a, b⟩ := hasDerivAt_rz hθ h1 h2
  set α := -(xp * Frames.Model.arcsec)
  set β := -(yp * Frames.Model.arcsec)
  have q := HasDerivAt.fun_add (HasDerivAt.const_mul (sin α) a) (HasDerivAt.const_mul (cos α) h3)
  simp only [earthVelocity, Frames.Model.earthFixed, Frames.Model.rx, Frames.Model.ry,
    Frames.Model.rz]
  refine ⟨?_, ?_, ?_⟩
  · exact (HasDerivAt.fun_sub (HasDerivAt.const_mul (cos α) a)
      (HasDerivAt.const_mul (sin α) h3)).congr_deriv (by ring)
  · exact (HasDerivAt.fun_add (HasDerivAt.const_mul (cos β) b)
      (HasDerivAt.const_mul (sin β) q)).congr_deriv (by ring)
  · exact (HasDerivAt.fun_add (HasDerivAt.const_mul (-sin β) b)
      (HasDerivAt.const_mul (cos β) q)).congr_deriv (by ring)

end Demos.Geolocation.Model
