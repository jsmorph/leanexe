import Project.EulerRiemann.Initial
import Project.EulerRiemann.RealRusanov

namespace Project.EulerRiemann.Initial
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DConservative.Guard (decodedState)
open Project.EulerRiemann.RealRusanov (energyMargin)
open CodeLib.IEEE64 (value)
open Wasm.IEEE64 (scaledValue)

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

def ScaledQuantitative (q : State) : Prop :=
  (2 : Int)^1074 ≤ 8 * scaledValue q.density ∧
  (2 : Int)^1074 ≤ 4 * scaledValue q.energy ∧
  |scaledValue q.density| ≤ 4 * (2 : Int)^1074 ∧
  |scaledValue q.mx| ≤ 4 * (2 : Int)^1074 ∧
  |scaledValue q.my| ≤ 4 * (2 : Int)^1074 ∧
  |scaledValue q.energy| ≤ 4 * (2 : Int)^1074 ∧
  (2 : Int)^2148 ≤ 100 * (2 * scaledValue q.density * scaledValue q.energy -
    (scaledValue q.mx)^2 - (scaledValue q.my)^2)

instance (q : State) : Decidable (ScaledQuantitative q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

noncomputable def Quantitative (q : State) : Prop :=
  (1 : ℝ) / 8 ≤ value q.density ∧ (1 : ℝ) / 4 ≤ value q.energy ∧
  (∀ i, |decodedState q.density q.mx q.my q.energy i| ≤ 4) ∧
  (1 : ℝ) / 100 ≤ energyMargin (decodedState q.density q.mx q.my q.energy)

theorem quantitative_of_scaled (q : State) (h : ScaledQuantitative q) :
    Quantitative q := by
  obtain ⟨hr, he, br, bx, byy, be, hm⟩ := h
  have hden : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have lower (word : UInt64) (factor : Nat)
      (hf : 0 < factor) (hw : (2 : Int)^1074 ≤ factor * scaledValue word) :
      1 / (factor : ℝ) ≤ value word := by
    have hw' : (2 : ℝ)^1074 ≤ (factor : ℝ) * (scaledValue word : ℝ) := by
      exact_mod_cast hw
    unfold value
    apply (le_div_iff₀ hden).mpr
    have hf' : (0 : ℝ) < factor := by exact_mod_cast hf
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ hf').mpr
    nlinarith only [hw']
  have bounded (word : UInt64) (hw : |scaledValue word| ≤ 4 * (2 : Int)^1074) :
      |value word| ≤ 4 := by
    simp only [value, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    exact_mod_cast hw
  refine ⟨lower q.density 8 (by decide) hr, lower q.energy 4 (by decide) he, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact bounded q.density br
    · exact bounded q.mx bx
    · exact bounded q.my byy
    · exact bounded q.energy be
  · have hm' : (2 : ℝ)^2148 ≤
        100 * (2 * (scaledValue q.density : ℝ) * (scaledValue q.energy : ℝ) -
          (scaledValue q.mx : ℝ)^2 - (scaledValue q.my : ℝ)^2) := by
      exact_mod_cast hm
    have hscale : (2 : ℝ)^2148 = ((2 : ℝ)^1074)^2 := by rw [← pow_mul]
    have heq : energyMargin (decodedState q.density q.mx q.my q.energy) *
        ((2 : ℝ)^1074)^2 =
        2 * (scaledValue q.density : ℝ) * (scaledValue q.energy : ℝ) -
          (scaledValue q.mx : ℝ)^2 - (scaledValue q.my : ℝ)^2 := by
      dsimp [energyMargin, decodedState, value]
      field_simp
    rw [hscale, ← heq] at hm'
    by_contra hlt
    have hproduct := mul_lt_mul_of_pos_right (lt_of_not_ge hlt)
      (sq_pos_of_pos hden)
    nlinarith only [hm', hproduct]

set_option maxHeartbeats 8000000 in
theorem weighted_scaled_quantitative : ∀ x y : Fin 6,
    ScaledQuantitative (weighted x.val y.val) := by
  intro x
  fin_cases x
  all_goals
    simp only [weighted, bottomLeft_eq, bottomRight_eq, topLeft_eq, topRight_eq]
    decide +kernel

theorem weighted_quantitative (x y : Fin 6) :
    Quantitative (weighted x.val y.val) :=
  quantitative_of_scaled _ (weighted_scaled_quantitative x y)

theorem initial_quantitative (n : Nat) (j i : Fin n) :
    Quantitative (initial n j i) :=
  weighted_quantitative
    ⟨LeanExe.Examples.EulerRiemann.lowerFractionNumerator n i.val,
      by have := Geometry.lowerFractionNumerator_le n i.val; omega⟩
    ⟨LeanExe.Examples.EulerRiemann.lowerFractionNumerator n j.val,
      by have := Geometry.lowerFractionNumerator_le n j.val; omega⟩

#print axioms quantitative_of_scaled
#print axioms weighted_scaled_quantitative
#print axioms initial_quantitative
end Project.EulerRiemann.Initial
