import Project.ExpArm.NormalPath
import Project.ProofKit.F64Accuracy

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Accuracy Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem normal_path_accuracy (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 512) :
    ErrorBelowOneUlp (normalPath x) (Real.exp (value x)) := by
  have h := normal_path_error x hf hx
  have hk : |reductionInteger x| ≤ (94721 : Int) := by
    have hb := reductionInteger_abs x hf (hx.trans (by norm_num))
    have hi : |(reductionInteger x : ℝ)| ≤ 94721 := by linarith
    exact_mod_cast hi
  have hm : 0 ≤ 1023+reductionInteger x/128 := by
    have hb := abs_le.mp hk
    omega
  dsimp only at h
  rw [scaleFactor_zpow _ hm] at h
  exact of_adjacent_binades _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem mask_index_nat (word : UInt64) :
    (2*(word &&& 127)).toNat = 2*(word &&& 127).toNat := by
  have h : (word &&& 127).toNat ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
  rw [UInt64.toNat_mul]
  change (2*(word &&& 127).toNat) % 2^64 = _
  omega

theorem exp_normal_path (x : UInt64)
    (hl : ¬x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000)
    (hu : x &&& 0x7FFFFFFFFFFFFFFF < 0x4080000000000000) : exp x = normalPath x := by
  have hb : ¬0x4090000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  have hs : ¬0x4080000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  simp only [exp, hl, hb, hs, ite_false, normalPath, normalReconstruction,
    reductionWord, reducedWord, correctionWord, mask_index_nat]

theorem tiny_accuracy (x : UInt64)
    (hx : x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000) :
    ErrorBelowOneUlp (exp x) (Real.exp (value x)) := by
  have h := tiny_error x hx
  have he := h.2.2
  rw [exp_tiny x hx, one_value] at he
  have habs := abs_lt.mp he
  apply of_adjacent_binades _ _ 0 h.2.1
  · norm_num
    linarith
  · norm_num
    linarith
  · simp only [zpow_zero]
    split
    · exact h.2.2
    · exact h.2.2.trans (by norm_num)

theorem exp_normal_accuracy (x : UInt64)
    (hx : x &&& 0x7FFFFFFFFFFFFFFF < 0x4080000000000000) :
    ErrorBelowOneUlp (exp x) (Real.exp (value x)) := by
  by_cases ht : x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000
  · exact tiny_accuracy x ht
  have hf : Finite x := (finiteBits_iff x).mp (by
    simp only [finiteBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, absBits] at *
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega)
  have hv : value 0x4080000000000000 = 512 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hb : |value x| ≤ 512 := by
    have h := abs_value_lt x 0x4080000000000000 hx
    rw [hv, abs_of_pos (by norm_num : (0 : ℝ) < 512)] at h
    exact h.le
  rw [exp_normal_path x ht hx]
  exact normal_path_accuracy x hf hb

#print axioms exp_normal_accuracy
end Project.ExpArm
