import CodeLib.IEEE64.Roundoff

namespace Project.ProofKit.F64Accuracy
open CodeLib.IEEE64

def ErrorBelowOneUlp (word : UInt64) (exact : ℝ) : Prop :=
  Finite word ∧ ∃ e : Int,
    (2 : ℝ)^e ≤ exact ∧ exact < (2 : ℝ)^(e+1) ∧
    |value word-exact| < max ((2 : ℝ)^(e-52)) ((2 : ℝ)^(-1074 : Int))

theorem of_adjacent_binades (word : UInt64) (exact : ℝ) (m : Int) (hf : Finite word)
    (hl : ((2 : ℝ)^m)/2 ≤ exact) (hu : exact < 2*((2 : ℝ)^m))
    (he : |value word-exact| < if exact < (2 : ℝ)^m then ((2 : ℝ)^m)/2^53
      else ((2 : ℝ)^m)/2^52) : ErrorBelowOneUlp word exact := by
  refine ⟨hf, ?_⟩
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  by_cases h : exact < (2 : ℝ)^m
  · rw [ite_eq_left h] at he
    refine ⟨m-1, ?_, ?_, ?_⟩
    · simpa only [zpow_sub₀ htwo, zpow_one] using hl
    · simpa only [sub_add_cancel] using h
    · apply he.trans_le
      have hp : (2 : ℝ)^(m-1-52) = ((2 : ℝ)^m)/2^53 := by
        rw [show m-1-52 = m-53 by omega, zpow_sub₀ htwo]
        rfl
      rw [hp]
      exact le_max_left _ _
  · rw [ite_eq_right h] at he
    refine ⟨m, le_of_not_gt h, ?_, ?_⟩
    · simpa only [zpow_add₀ htwo, zpow_one, mul_comm] using hu
    · apply he.trans_le
      rw [zpow_sub₀ htwo]
      exact le_max_left _ _

end Project.ProofKit.F64Accuracy
