import Project.ExpNeg.Numerical

namespace Project.ExpNeg
open CodeLib.IEEE64 Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem inDomain_iff (x : UInt64) : inDomain x = true ↔ Finite x ∧ value x ≤ 0 := by
  have hn := x.toNat_lt
  constructor
  · intro h
    simp only [inDomain, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with rfl | ⟨hs, ht⟩
    · exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by rw [ExpSmall.zero_value]⟩
    have hsign : Wasm.IEEE64.sign x = true := by
      have hh : 2^63 ≤ x.toNat := UInt64.le_iff_toNat_le.mp hs
      simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hh
    have hf : Finite x := (finiteBits_iff x).mp (by
      simp only [finiteBits, decide_eq_true_eq]
      rw [UInt64.lt_iff_toNat_lt, absBits_toNat]
      have hs' := UInt64.le_iff_toNat_le.mp hs
      have ht' := UInt64.lt_iff_toNat_lt.mp ht
      norm_num [UInt64.toNat_ofNat] at hs' ht' hn ⊢
      omega)
    refine ⟨hf, ?_⟩
    simp only [value, Wasm.IEEE64.scaledValue, hsign, ite_true, Int.cast_neg, Int.cast_natCast]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)
  · rintro ⟨hf, hu⟩
    by_cases hz : x = 0
    · simp [inDomain, hz]
    have hs : (0x8000000000000000 : UInt64) ≤ x := by
      by_contra h
      have ht : x.toNat < 2^63 := Nat.lt_of_not_ge (UInt64.le_iff_toNat_le.not.mp h)
      have habs : absBits x = x := by
        apply UInt64.toNat.inj
        rw [absBits_toNat, Nat.mod_eq_of_lt ht]
      have hp : absBits 0 < absBits x := by
        rw [habs, UInt64.lt_iff_toNat_lt]
        change 0 < x.toNat
        have hne : x.toNat ≠ 0 := fun hh => hz (UInt64.toNat.inj hh)
        omega
      have hv := abs_value_lt 0 x hp
      have hsign : Wasm.IEEE64.sign x = false := by
        simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using ht
      have hnonneg : 0 ≤ value x := by
        simp only [value, Wasm.IEEE64.scaledValue, hsign, Bool.false_eq_true, ite_false, Int.cast_natCast]
        positivity
      rw [ExpSmall.zero_value, abs_zero, abs_of_nonneg hnonneg] at hv
      linarith
    have ht : x < (0xFFF0000000000000 : UInt64) := by
      have hh := (finiteBits_iff x).mpr hf
      simp only [finiteBits, decide_eq_true_eq] at hh
      rw [UInt64.lt_iff_toNat_lt, absBits_toNat] at hh
      have hs' := UInt64.le_iff_toNat_le.mp hs
      rw [UInt64.lt_iff_toNat_lt]
      norm_num [UInt64.toNat_ofNat] at hs' hh hn ⊢
      omega
    simp [inDomain, hs, ht]

#print axioms inDomain_iff
end Project.ExpNeg
