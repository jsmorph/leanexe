import Project.ProofKit.F64StrictOrder

namespace Project.ProofKit.F64Order
open CodeLib.IEEE64

theorem positiveBits_of_finite_value_pos (bits : UInt64)
    (hf : Finite bits) (hp : 0 < value bits) : positiveBits bits = true := by
  have hsign : Wasm.IEEE64.sign bits = false := by
    by_contra h
    have ht : Wasm.IEEE64.sign bits = true := Bool.eq_true_of_not_eq_false h
    have hnonpos : value bits ≤ 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, ht, ite_true, Int.cast_neg,
        Int.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)
    linarith
  have hsmall : bits.toNat < 2^63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hsign
  have habs : absBits bits = bits := by
    apply UInt64.toNat_inj.mp
    rw [absBits_toNat, Nat.mod_eq_of_lt hsmall]
  have hnonzero : bits ≠ 0 := by
    intro hz
    subst bits
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at hp
  have hFinite := (finiteBits_iff bits).mpr hf
  have hnonzeroNat : bits.toNat ≠ 0 := by
    intro h
    exact hnonzero (UInt64.toNat_inj.mp h)
  simp only [finiteBits, habs, decide_eq_true_eq] at hFinite
  simp only [positiveBits, Bool.and_eq_true_iff, decide_eq_true_eq]
  exact ⟨UInt64.lt_iff_toNat_lt.mpr (Nat.pos_of_ne_zero hnonzeroNat), hFinite⟩

theorem positiveBits_iff (bits : UInt64) :
    positiveBits bits = true ↔ Finite bits ∧ 0 < value bits :=
  ⟨positiveBits_spec bits, fun h => positiveBits_of_finite_value_pos bits h.1 h.2⟩

theorem positive_word_lt_iff (left right : UInt64)
    (hl : positiveBits left = true) (hr : positiveBits right = true) :
    left < right ↔ value left < value right := by
  constructor
  · intro h
    have hValue := abs_value_lt left right (by
      simpa only [absBits_of_positive left hl, absBits_of_positive right hr] using h)
    simpa only [abs_of_pos (positiveBits_spec left hl).2,
      abs_of_pos (positiveBits_spec right hr).2] using hValue
  · intro h
    by_contra hn
    have hReverse : right ≤ left := by
      rw [UInt64.le_iff_toNat_le]
      rw [UInt64.lt_iff_toNat_lt] at hn
      omega
    have hValue := abs_value_mono right left (by
      simpa only [absBits_of_positive left hl, absBits_of_positive right hr] using hReverse)
    rw [abs_of_pos (positiveBits_spec left hl).2,
      abs_of_pos (positiveBits_spec right hr).2] at hValue
    exact (not_le_of_gt h) hValue

#print axioms positiveBits_of_finite_value_pos
#print axioms positiveBits_iff
#print axioms positive_word_lt_iff
end Project.ProofKit.F64Order
