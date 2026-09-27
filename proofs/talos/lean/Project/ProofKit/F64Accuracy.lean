import CodeLib.IEEE64.Roundoff
import Mathlib.Data.Int.Log

namespace Project.ProofKit.F64Accuracy
open CodeLib.IEEE64

def ErrorBelowOneUlp (word : UInt64) (exact : ℝ) : Prop :=
  Finite word ∧ ∃ e : Int,
    (2 : ℝ)^e ≤ exact ∧ exact < (2 : ℝ)^(e+1) ∧
    |value word-exact| < max ((2 : ℝ)^(e-52)) ((2 : ℝ)^(-1074 : Int))

theorem of_subnormal_error (word : UInt64) (exact : ℝ) (hf : Finite word) (hp : 0 < exact)
    (he : |value word-exact| < (2 : ℝ)^(-1074 : Int)) : ErrorBelowOneUlp word exact := by
  exact ⟨hf, Int.log 2 exact, Int.zpow_log_le_self (by decide) hp,
    Int.lt_zpow_succ_log_self (by decide) exact, he.trans_le (le_max_right _ _)⟩

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

theorem of_scaled_adjacent_binades (word core : UInt64) (y : ℝ) (m p : Int)
    (hf : Finite word) (hv : value word = value core*(2 : ℝ)^p)
    (hl : ((2 : ℝ)^m)/2 ≤ y) (hu : y < 2*((2 : ℝ)^m))
    (he : |value core-y| < if y < (2 : ℝ)^m then ((2 : ℝ)^m)/2^53
      else ((2 : ℝ)^m)/2^52) : ErrorBelowOneUlp word (y*(2 : ℝ)^p) := by
  have hs : 0 < (2 : ℝ)^p := by positivity
  apply of_adjacent_binades word _ (m+p) hf
  · rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simpa only [div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hl hs.le
  · rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simpa only [mul_assoc] using mul_lt_mul_of_pos_right hu hs
  · rw [hv, ← sub_mul, abs_mul, abs_of_pos hs,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [mul_lt_mul_iff_left₀ hs]
    have h := mul_lt_mul_of_pos_right he hs
    by_cases hy : y < (2 : ℝ)^m
    all_goals simp only [hy, ite_true, ite_false] at h ⊢
    all_goals simpa only [div_mul_eq_mul_div] using h

theorem lower_of_rounded_power (word : UInt64) (y : ℝ) (m q : Int)
    (hw : (2 : ℝ)^q ≤ value word) (hl : (2 : ℝ)^m/2 ≤ y)
    (he : |value word-y| < if y < (2 : ℝ)^m then (2 : ℝ)^m/2^53
      else (2 : ℝ)^m/2^52) :
    (2 : ℝ)^q-(2 : ℝ)^(q-53) < y := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hp : 0 < (2 : ℝ)^(q-53) := by positivity
  by_cases hy : (2 : ℝ)^q ≤ y
  · linarith
  have hy' : y < (2 : ℝ)^q := lt_of_not_ge hy
  have hm : m ≤ q := by
    by_contra hn
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show q+1 ≤ m by omega)
    have h' := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
    have hid : (2 : ℝ)^(q+1)/2 = (2 : ℝ)^q := by rw [zpow_add₀ htwo]; norm_num
    rw [hid] at h'
    linarith
  have herr : |value word-y| < (2 : ℝ)^(q-53) := by
    by_cases heq : m = q
    · subst m
      rw [ite_eq_left hy', zpow_sub₀ htwo] at *
      exact he
    · have hupper : (2 : ℝ)^m/2^52 ≤ (2 : ℝ)^(q-53) := by
        rw [show (2 : ℝ)^m/2^52 = (2 : ℝ)^(m-52) by rw [zpow_sub₀ htwo]; rfl]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      apply lt_of_lt_of_le _ hupper
      split at he
      · exact he.trans (div_lt_div_of_pos_left (by positivity) (by positivity) (by norm_num))
      · exact he
  have h := (abs_lt.mp herr).2
  linarith

end Project.ProofKit.F64Accuracy
