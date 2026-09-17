import Project.F64Clip.Scalar
import Project.ProofKit.F64OrderComplete

namespace Project.F64Clip
open CodeLib.IEEE64 Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem zero_value : value (0 : UInt64) = 0 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]

theorem ten_value : value (0x4024000000000000 : UInt64) = 10 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem bound_sign_iff (bound : UInt64) (hf : Finite bound) :
    (bound < 0x8000000000000000 ∨ absBits bound = 0) ↔ 0 ≤ value bound := by
  constructor
  · rintro (hs | hz)
    · exact value_nonnegative bound hs
    · have h := absBits_value bound
      rw [hz, zero_value] at h
      exact (abs_eq_zero.mp h.symm).ge
  · intro h
    by_cases hp : 0 < value bound
    · left
      have hb := positiveBits_of_finite_value_pos bound hf hp
      have hi : (0 : UInt64) < bound ∧ bound < 0x7FF0000000000000 := by
        simpa only [positiveBits, Bool.and_eq_true, decide_eq_true_eq] using hb
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat] at hi ⊢
      norm_num at hi ⊢
      omega
    · right
      have hz : value bound = 0 := by linarith
      have hraw := (absBits_le_iff bound 0 (by unfold CodeLib.IEEE64.Finite; decide)).mpr
        ⟨hf, by rw [hz, zero_value]⟩
      have hzero : absBits (0 : UInt64) = 0 := by decide
      rw [hzero, UInt64.le_iff_toNat_le] at hraw
      apply UInt64.toNat_inj.mp
      simpa using Nat.eq_zero_of_le_zero hraw

theorem validBound_iff (bound : UInt64) :
    validBound bound = true ↔ Finite bound ∧ 0 ≤ value bound ∧ value bound ≤ 10 := by
  have ht : Finite (0x4024000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  have ha : absBits (0x4024000000000000 : UInt64) = 0x4024000000000000 := by decide
  simp only [validBound, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, finiteBits_iff]
  constructor
  · rintro ⟨⟨hf, hs⟩, hm⟩
    have h0 := (bound_sign_iff bound hf).mp hs
    have hb := (absBits_le_iff bound _ ht).mp (by simpa only [ha] using hm)
    rw [ten_value, abs_of_nonneg h0, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10)] at hb
    exact ⟨hf, h0, hb.2⟩
  · rintro ⟨hf, h0, hm⟩
    refine ⟨⟨hf, (bound_sign_iff bound hf).mpr h0⟩, ?_⟩
    have hb := (absBits_le_iff bound _ ht).mpr ⟨hf, by
      rw [ten_value, abs_of_nonneg h0, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10)]
      exact hm⟩
    simpa only [ha] using hb

#print axioms validBound_iff
end Project.F64Clip
