import Project.Euler2DConservative.RealHyperbolicity

namespace Project.Euler2DConservative.RealFlux
open Guard (Vec4 Admissible)

theorem max_acoustic_abs (u c : ℝ) (hc : 0 ≤ c) :
    max |u-c| |u+c| = |u|+c := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu, abs_of_nonneg (add_nonneg hu hc)]
    exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
  · have hn : u ≤ 0 := le_of_not_ge hu
    rw [abs_of_nonpos hn, abs_of_nonpos (by linarith : u-c ≤ 0)]
    have h : |u+c| ≤ -(u-c) := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [max_eq_left h]
    ring

theorem eigenvalue_abs_le (u c : ℝ) (hc : 0 ≤ c) (i : Fin 4) :
    |eigenvalues u c i| ≤ |u|+c := by
  have h := max_acoustic_abs u c hc
  have hl : |u-c| ≤ |u|+c := h ▸ le_max_left |u-c| |u+c|
  have hr : |u+c| ≤ |u|+c := h ▸ le_max_right |u-c| |u+c|
  fin_cases i
  · exact hl
  · exact le_add_of_nonneg_right hc
  · exact le_add_of_nonneg_right hc
  · exact hr

theorem eigenvalue_bound_iff (u c a : ℝ) (hc : 0 ≤ c) :
    (∀ i, |eigenvalues u c i| ≤ a) ↔ |u|+c ≤ a := by
  constructor
  · intro h
    rw [← max_acoustic_abs u c hc]
    exact max_le (h 0) (h 3)
  · intro h i
    exact (eigenvalue_abs_le u c hc i).trans h

noncomputable def characteristicSpeed (n : Direction) (U : Vec4) : ℝ :=
  |normalVelocity n U|+soundSpeed U

theorem characteristicSpeed_pos (n : Direction) (U : Vec4) (hU : Admissible U) :
    0 < characteristicSpeed n U :=
  add_pos_of_nonneg_of_pos (abs_nonneg _) (soundSpeed_pos U hU)

theorem directional_speed_bound_iff (n : Direction) (U : Vec4) (a : ℝ) :
    (∀ i, |eigenvalues (normalVelocity n U) (soundSpeed U) i| ≤ a) ↔
      characteristicSpeed n U ≤ a :=
  eigenvalue_bound_iff _ _ _ (Real.sqrt_nonneg _)

#print axioms max_acoustic_abs
#print axioms directional_speed_bound_iff
end Project.Euler2DConservative.RealFlux
