import Project.ProofKit.F64Adjacent

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
open Project.ProofKit.F64Order
set_option exponentiation.threshold 4096

theorem negative_word_value (bits : UInt64) (h : 2^63 ≤ bits.toNat) :
    value bits = -(unsignedScaled (bits.toNat-2^63) : ℝ)/(2:ℝ)^1074 := by
  have hs : Wasm.IEEE64.sign bits = true := by
    simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using h
  have hb := bits.toNat_lt
  have hm : Wasm.IEEE64.scaledMagnitude bits = unsignedScaled (bits.toNat-2^63) := by
    rw [scaledMagnitude_abs, absBits_toNat, show bits.toNat%2^63 = bits.toNat-2^63 by omega]
  simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg,
    Int.cast_natCast, hm]

theorem word_pred_nat (bits : UInt64) (h : 0 < bits.toNat) :
    (bits-1).toNat = bits.toNat-1 := by
  exact UInt64.toNat_sub_of_le bits 1 (UInt64.le_iff_toNat_le.mpr h)

theorem word_succ_nat (bits : UInt64) (h : bits.toNat+1 < 2^64) :
    (bits+1).toNat = bits.toNat+1 := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem positive_predecessor_gap (bits : UInt64)
    (h : 0 < bits.toNat ∧ bits.toNat < 2^63) :
    value bits-value (bits-1) =
      (2:ℝ)^((bits.toNat-1)/2^52-1)/(2:ℝ)^1074 := by
  have hp := word_pred_nat bits h.1
  have hm := unsignedScaled_succ (bits.toNat-1)
  rw [Nat.sub_add_cancel h.1] at hm
  rw [unsigned_word_value bits h.2, unsigned_word_value (bits-1) (by omega), hp, hm]
  push_cast
  ring

theorem negative_successor_gap (bits : UInt64) (h : 2^63 < bits.toNat) :
    value (bits-1)-value bits =
      (2:ℝ)^((bits.toNat-2^63-1)/2^52-1)/(2:ℝ)^1074 := by
  have hp := word_pred_nat bits (by omega)
  have hm := unsignedScaled_succ (bits.toNat-2^63-1)
  rw [show bits.toNat-2^63-1+1 = bits.toNat-2^63 by omega] at hm
  rw [negative_word_value bits (by omega), negative_word_value (bits-1) (by omega), hp,
    show bits.toNat-1-2^63 = bits.toNat-2^63-1 by omega, hm]
  push_cast
  ring

theorem negative_predecessor_gap (bits : UInt64)
    (h : 2^63 ≤ bits.toNat ∧ bits.toNat+1 < 2^64) :
    value bits-value (bits+1) =
      (2:ℝ)^((bits.toNat-2^63)/2^52-1)/(2:ℝ)^1074 := by
  have hp := word_succ_nat bits h.2
  rw [negative_word_value bits h.1, negative_word_value (bits+1) (by omega), hp,
    show bits.toNat+1-2^63 = (bits.toNat-2^63)+1 by omega, unsignedScaled_succ]
  push_cast
  ring

theorem finite_word_bound (bits : UInt64) (h : Finite bits) :
    bits.toNat%2^63 < 0x7FF0000000000000 := by
  have hf := (finiteBits_iff bits).mpr h
  simp only [finiteBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, absBits_toNat] at hf
  exact hf

theorem nextUp_lt (bits : UInt64) (h : Finite bits) :
    value bits < value (nextUp bits) := by
  have hb := finite_word_bound bits h
  have hn := bits.toNat_lt
  by_cases hz : bits = 0x8000000000000000
  · subst bits
    rw [zero_endpoints.2.1, unsigned_word_value 1 (by decide),
      negative_word_value 0x8000000000000000 (by decide)]
    rw [show unsignedScaled ((0x8000000000000000:UInt64).toNat-2^63) = 0 by decide +kernel,
      show unsignedScaled (1:UInt64).toNat = 1 by decide +kernel]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  · by_cases hs : bits.toNat < 2^63
    · exact nextUp_nonnegative_lt bits (by omega)
    · have hne : bits.toNat ≠ 2^63 := by
        intro he
        exact hz (UInt64.toNat_inj.mp he)
      have hg := negative_successor_gap bits (by omega)
      have hp : (0:ℝ) < (2:ℝ)^((bits.toNat-2^63-1)/2^52-1)/(2:ℝ)^1074 := by positivity
      have hw : ¬bits < 0x8000000000000000 := by
        intro hw
        exact hs (UInt64.lt_iff_toNat_lt.mp hw)
      simp only [nextUp, hz, ite_false, hw]
      linarith

theorem nextDown_lt (bits : UInt64) (h : Finite bits) :
    value (nextDown bits) < value bits := by
  have hb := finite_word_bound bits h
  have hn := bits.toNat_lt
  by_cases hz : bits = 0
  · subst bits
    rw [zero_endpoints.2.2.1, unsigned_word_value 0 (by decide),
      negative_word_value 0x8000000000000001 (by decide)]
    rw [show unsignedScaled ((0x8000000000000001:UInt64).toNat-2^63) = 1 by decide +kernel,
      show unsignedScaled (0:UInt64).toNat = 0 by decide +kernel]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  · have hne : 0 < bits.toNat := by
      have hh : bits.toNat ≠ 0 := fun he => hz (UInt64.toNat_inj.mp he)
      omega
    by_cases hs : bits.toNat < 2^63
    · have hg := positive_predecessor_gap bits ⟨hne, hs⟩
      have hp : (0:ℝ) < (2:ℝ)^((bits.toNat-1)/2^52-1)/(2:ℝ)^1074 := by positivity
      have hw : bits < 0x8000000000000000 := UInt64.lt_iff_toNat_lt.mpr hs
      simp only [nextDown, hz, ite_false, hw, ite_true]
      linarith
    · have hg := negative_predecessor_gap bits ⟨by omega, by omega⟩
      have hp : (0:ℝ) < (2:ℝ)^((bits.toNat-2^63)/2^52-1)/(2:ℝ)^1074 := by positivity
      have hw : ¬bits < 0x8000000000000000 := by
        intro hw
        exact hs (UInt64.lt_iff_toNat_lt.mp hw)
      simp only [nextDown, hz, ite_false, hw]
      linarith

#print axioms negative_successor_gap
#print axioms negative_predecessor_gap
#print axioms nextUp_lt
#print axioms nextDown_lt
end Project.ProofKit.F64Adjacent
