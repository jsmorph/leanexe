import Project.ExpSmall.Numerical
import Project.ProofKit.F64StrictOrder

namespace Project.ExpSmall
open CodeLib.IEEE64 Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem one_value : value 0x3FF0000000000000 = 1 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem zero_value : value 0 = 0 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem inDomain_sound (x : UInt64) (h : inDomain x = true) :
    Finite x ∧ -1 ≤ value x ∧ value x ≤ 0 := by
  simp only [inDomain, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with rfl | ⟨hl, hu⟩
  · exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by rw [zero_value]; norm_num, by rw [zero_value]⟩
  have hl' := UInt64.le_iff_toNat_le.mp hl
  have hu' := UInt64.le_iff_toNat_le.mp hu
  norm_num [UInt64.toNat_ofNat] at hl' hu'
  have hb : absBits x ≤ 0x3FF0000000000000 := by
    rw [UInt64.le_iff_toNat_le, absBits_toNat]
    change x.toNat % 2^63 ≤ 4607182418800017408
    change 9223372036854775808 ≤ x.toNat at hl'
    change x.toNat ≤ 13830554455654793216 at hu'
    omega
  have hf : Finite x := (finiteBits_iff x).mp (by
    simp only [finiteBits, decide_eq_true_eq]
    rw [UInt64.lt_iff_toNat_lt]
    have hb' := UInt64.le_iff_toNat_le.mp hb
    norm_num [UInt64.toNat_ofNat] at hb' ⊢
    omega)
  have bm : |value x| ≤ 1 := by
    have ho : absBits 0x3FF0000000000000 = 0x3FF0000000000000 := by decide
    have h := abs_value_mono x 0x3FF0000000000000 (by rw [ho]; exact hb)
    simpa [one_value] using h
  have hs : Wasm.IEEE64.sign x = true := by
    simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hl'
  refine ⟨hf, (abs_le.mp bm).1, ?_⟩
  simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem inDomain_complete (x : UInt64) (hl : -1 ≤ value x) (hu : value x ≤ 0) :
    inDomain x = true := by
  by_cases hz : x = 0
  · simp [inDomain, hz]
  have hn : x.toNat < 2^64 := x.toNat_lt
  have hs : (0x8000000000000000 : UInt64) ≤ x := by
    by_contra h
    have ht : x.toNat < 2^63 := by
      rw [UInt64.le_iff_toNat_le] at h
      exact Nat.lt_of_not_ge h
    have hb : absBits x = x := by
      apply UInt64.toNat.inj
      rw [absBits_toNat, Nat.mod_eq_of_lt ht]
    have hp : absBits 0 < absBits x := by
      rw [hb]
      change (0 : UInt64) < x
      rw [UInt64.lt_iff_toNat_lt]
      change 0 < x.toNat
      have : x.toNat ≠ 0 := by intro h; apply hz; exact UInt64.toNat.inj h
      omega
    have hv := abs_value_lt 0 x hp
    have hsign : Wasm.IEEE64.sign x = false := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
      exact Nat.not_le.mpr ht
    have hnonneg : 0 ≤ value x := by
      simp only [value, Wasm.IEEE64.scaledValue, hsign, Bool.false_eq_true, ite_false,
        Int.cast_natCast]
      positivity
    rw [zero_value, abs_zero, abs_of_nonneg hnonneg] at hv
    linarith
  have hb : x ≤ (0xBFF0000000000000 : UInt64) := by
    by_contra h
    have hp : absBits 0x3FF0000000000000 < absBits x := by
      rw [UInt64.lt_iff_toNat_lt, absBits_toNat, absBits_toNat]
      have hsn := UInt64.le_iff_toNat_le.mp hs
      have hbn := UInt64.le_iff_toNat_le.not.mp h
      norm_num [UInt64.toNat_ofNat] at hsn hbn ⊢
      omega
    have hv := abs_value_lt 0x3FF0000000000000 x hp
    rw [one_value, abs_one, abs_of_nonpos hu] at hv
    linarith
  simp [inDomain, hs, hb]

theorem inDomain_iff (x : UInt64) :
    inDomain x = true ↔ Finite x ∧ -1 ≤ value x ∧ value x ≤ 0 :=
  ⟨inDomain_sound x, fun h => inDomain_complete x h.2.1 h.2.2⟩

theorem expSmall_success (x : UInt64) (hl : -1 ≤ value x) (hu : value x ≤ 0) :
    (expSmall x).status = 0 ∧ (expSmall x).bits = polynomial x := by
  simp [expSmall, inDomain_complete x hl hu]

theorem expSmall_zero : expSmall 0 = ⟨0, 0x3FF0000000000000⟩ := by decide +kernel
theorem expSmall_negative_zero : expSmall 0x8000000000000000 = ⟨0, 0x3FF0000000000000⟩ := by
  decide +kernel

#print axioms inDomain_iff
#print axioms expSmall_success
#print axioms expSmall_zero
#print axioms expSmall_negative_zero
end Project.ExpSmall
