import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Demos.Frames.Model

/-!
The measurement model of `requirements.md` over the real numbers: the distance from a receiver to
the emitter, the range rate, and the models of a time difference and a frequency difference of
arrival.  `range_hasDerivAt` (M1) states that the range rate is the time derivative of the
distance along a receiver's trajectory, for an emitter fixed in the frame of the trajectory.
-/

open Real

namespace Demos.Geolocation.Model

abbrev V3 := ℝ × ℝ × ℝ

/-- The speed of light in km/s. -/
noncomputable def c : ℝ := 299792.458

/-- The distance from the receiver at `s` to the emitter at `x`. -/
noncomputable def range (s x : V3) : ℝ :=
  √((s.1 - x.1) ^ 2 + (s.2.1 - x.2.1) ^ 2 + (s.2.2 - x.2.2) ^ 2)

/-- The rate of change of the distance for a receiver at `s` with velocity `u`. -/
noncomputable def rangeRate (s u x : V3) : ℝ :=
  ((s.1 - x.1) * u.1 + (s.2.1 - x.2.1) * u.2.1 + (s.2.2 - x.2.2) * u.2.2) / range s x

/-- The time difference of arrival at receiver `i` less receiver `j`, in seconds. -/
noncomputable def tdoa (si sj x : V3) : ℝ := (range si x - range sj x) / c

/-- The frequency difference of arrival at receiver `i` less receiver `j`, in Hz, for the
carrier frequency `f`: the first-order Doppler shift `−f ρ̇ᵢ / c` less `−f ρ̇ⱼ / c`. -/
noncomputable def fdoa (f : ℝ) (si ui sj uj x : V3) : ℝ :=
  -(f * (rangeRate si ui x - rangeRate sj uj x)) / c

/-- **M1.**  For a receiver whose coordinates `s₁`, `s₂`, `s₃` have the derivatives `u` at `t`,
and an emitter `x` away from it, the derivative of the distance at `t` is the range rate. -/
theorem range_hasDerivAt {s₁ s₂ s₃ : ℝ → ℝ} {u x : V3} {t : ℝ} (h1 : HasDerivAt s₁ u.1 t)
    (h2 : HasDerivAt s₂ u.2.1 t) (h3 : HasDerivAt s₃ u.2.2 t) (hne : (s₁ t, s₂ t, s₃ t) ≠ x) :
    HasDerivAt (fun t => range (s₁ t, s₂ t, s₃ t) x) (rangeRate (s₁ t, s₂ t, s₃ t) u x) t := by
  have q := HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_pow (HasDerivAt.sub_const x.1 h1) 2)
    (HasDerivAt.fun_pow (HasDerivAt.sub_const x.2.1 h2) 2))
    (HasDerivAt.fun_pow (HasDerivAt.sub_const x.2.2 h3) 2)
  have hpos : s₁ t - x.1 ≠ 0 ∨ s₂ t - x.2.1 ≠ 0 ∨ s₃ t - x.2.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Prod.ext (by simp; linarith [h.1])
      (Prod.ext (by simp; linarith [h.2.1]) (by simp; linarith [h.2.2])))
  have hq : 0 < (s₁ t - x.1) ^ 2 + (s₂ t - x.2.1) ^ 2 + (s₃ t - x.2.2) ^ 2 := by
    have a := sq_nonneg (s₁ t - x.1)
    have b := sq_nonneg (s₂ t - x.2.1)
    have d := sq_nonneg (s₃ t - x.2.2)
    rcases hpos with h | h | h
    · linarith [lt_of_le_of_ne a (Ne.symm (pow_ne_zero 2 h))]
    · linarith [lt_of_le_of_ne b (Ne.symm (pow_ne_zero 2 h))]
    · linarith [lt_of_le_of_ne d (Ne.symm (pow_ne_zero 2 h))]
  have hs0 := Real.sqrt_pos.mpr hq
  unfold rangeRate range
  refine (HasDerivAt.sqrt q hq.ne').congr_deriv ?_
  have e : ∀ a : ℝ, a ^ (2 - 1) = a := fun a => by norm_num
  dsimp only
  simp only [e, Nat.cast_ofNat]
  rw [div_eq_div_iff (by positivity) hs0.ne']
  ring

end Demos.Geolocation.Model
