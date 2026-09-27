import Project.ExpArm.BranchWords
import Project.ExpArm.OuterRealBounds

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit F64Order

set_option exponentiation.threshold 4096

def ResultAccuracy (x result : UInt64) : Prop :=
  F64Accuracy.ErrorBelowOneUlp result (Real.exp (value x)) ∨
    result = 0x7FF0000000000000 ∧ (2 : ℝ)^1024-(2 : ℝ)^971 < Real.exp (value x)

theorem value_512 : value 0x4080000000000000 = 512 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
    Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem value_1024 : value 0x4090000000000000 = 1024 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
    Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem top_zero_nonnegative (x : UInt64) (hx : x >>> 63 = 0) : 0 ≤ value x := by
  have hn := congrArg UInt64.toNat hx
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.shiftRight_eq_div_pow] at hn
  have hs : Wasm.IEEE64.sign x = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
    omega
  simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false, Int.cast_natCast]
  positivity

theorem top_nonzero_nonpositive (x : UInt64) (hx : x >>> 63 ≠ 0) : value x ≤ 0 := by
  have hn : x.toNat/2^63 ≠ 0 := by
    intro h
    apply hx
    apply UInt64.toNat_inj.mp
    simpa only [UInt64.toNat_shiftRight, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow] using h
  have hs : Wasm.IEEE64.sign x = true := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
    omega
  simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem exp_accuracy (x : UInt64) (hf : Finite x) : ResultAccuracy x (exp x) := by
  by_cases hnormal : x &&& 0x7FFFFFFFFFFFFFFF < 0x4080000000000000
  · exact Or.inl (exp_normal_accuracy x hnormal)
  have h512 : 0x4080000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
    omega
  by_cases hmain : x &&& 0x7FFFFFFFFFFFFFFF < 0x4090000000000000
  · have habsl : 512 ≤ |value x| := by
      have h := abs_value_mono 0x4080000000000000 x h512
      simpa only [value_512, abs_of_pos (by norm_num : (0 : ℝ) < 512)] using h
    have habsu : |value x| < 1024 := by
      have h := abs_value_lt x 0x4090000000000000 hmain
      simpa only [value_1024, abs_of_pos (by norm_num : (0 : ℝ) < 1024)] using h
    by_cases hpos : 0 ≤ value x
    · rw [abs_of_nonneg hpos] at habsl habsu
      have hx : 512 ≤ value x ∧ value x ≤ 1024 := ⟨habsl, habsu.le⟩
      rw [exp_positive_path x h512 hmain (positive_reduction_sign x hf hx)]
      by_cases hsmall : value x ≤ 800
      · exact positive_path_accuracy x hf ⟨habsl, hsmall⟩
      · have hx800 : 800 ≤ value x := by linarith
        exact Or.inr ⟨positive_outer_path x hf ⟨hx800, habsu.le⟩,
          (by have he := real_exp_large (value x) hx800; linarith)⟩
    · have hn : value x < 0 := lt_of_not_ge hpos
      rw [abs_of_neg hn] at habsl habsu
      have hx : -1024 ≤ value x ∧ value x ≤ -512 := ⟨by linarith, by linarith⟩
      rw [exp_negative_path x h512 hmain (negative_reduction_sign x hf hx)]
      by_cases hsmall : -800 ≤ value x
      · exact Or.inl (negative_path_accuracy x hf ⟨hsmall, hx.2⟩)
      · have hx800 : value x ≤ -800 := by linarith
        rw [negative_outer_path x hf ⟨hx.1, hx800⟩]
        exact Or.inl (zero_accuracy (value x) hx800)
  · have h1024 : 0x4090000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF := by
      simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
      omega
    have habs : 1024 ≤ |value x| := by
      have h := abs_value_mono 0x4090000000000000 x h1024
      simpa only [value_1024, abs_of_pos (by norm_num : (0 : ℝ) < 1024)] using h
    have hmax : x &&& 0x7FFFFFFFFFFFFFFF ≤ 0x7FF0000000000000 := by
      have h := (finiteBits_iff x).mpr hf
      simp only [finiteBits, decide_eq_true_eq, absBits, UInt64.lt_iff_toNat_lt] at h
      rw [UInt64.le_iff_toNat_le]
      omega
    rw [exp_large x h1024 hmax]
    by_cases htop : x >>> 63 = 0
    · rw [ite_eq_left htop]
      rw [abs_of_nonneg (top_zero_nonnegative x htop)] at habs
      exact Or.inr ⟨rfl, by have he := real_exp_large (value x) (by linarith); linarith⟩
    · rw [ite_eq_right htop]
      rw [abs_of_nonpos (top_nonzero_nonpositive x htop)] at habs
      exact Or.inl (zero_accuracy (value x) (by linarith))

#print axioms exp_accuracy
end Project.ExpArm
