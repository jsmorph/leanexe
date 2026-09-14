import Project.ProofKit.F64MagnitudeEnclosure

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
open Project.ProofKit.F64Order
set_option exponentiation.threshold 4096

theorem nonnegative_enclosure (bits : UInt64) (shift : Nat) (x : ℝ)
    (hf : Finite bits) (hs : Wasm.IEEE64.sign bits = false) (hx : 0 ≤ x)
    (hn : shift = 0 ∨ 2^52*2^shift ≤ Wasm.IEEE64.scaledMagnitude bits)
    (he : |(Wasm.IEEE64.scaledMagnitude bits : ℝ)-x| ≤ (2:ℝ)^shift/2) :
    value (nextDown bits) ≤ x/(2:ℝ)^1074 ∧ x/(2:ℝ)^1074 ≤ value (nextUp bits) := by
  have hb := finite_word_bound bits hf
  have hsmall : bits.toNat < 2^63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hm : Wasm.IEEE64.scaledMagnitude bits = unsignedScaled bits.toNat := by
    rw [scaledMagnitude_abs, absBits_toNat, Nat.mod_eq_of_lt hsmall]
  rw [hm] at hn he
  obtain ⟨hl, hu⟩ := magnitude_enclosure bits.toNat shift x hx hn he
  have hp : bits.toNat+1 < 2^63 := by omega
  have hpn := word_succ_nat bits (by omega)
  constructor
  · by_cases hz : bits = 0
    · subst bits
      rw [zero_endpoints.2.2.1, negative_word_value 0x8000000000000001 (by decide),
        show unsignedScaled ((0x8000000000000001:UInt64).toNat-2^63) = 1 by decide +kernel]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    · have hpos : 0 < bits.toNat := by
        have hne : bits.toNat ≠ 0 := fun h => hz (UInt64.toNat_inj.mp h)
        omega
      have hpred := word_pred_nat bits hpos
      have hw : bits < 0x8000000000000000 := UInt64.lt_iff_toNat_lt.mpr hsmall
      simp only [nextDown, hz, ite_false, hw, ite_true]
      rw [unsigned_word_value (bits-1) (by omega), hpred]
      exact div_le_div_of_nonneg_right (by simpa only [show bits.toNat ≠ 0 by omega,
        ite_false] using hl) (by positivity)
  · rw [nextUp_nonnegative_eq bits hsmall, unsigned_word_value (bits+1) (by omega), hpn]
    exact div_le_div_of_nonneg_right hu (by positivity)

theorem negative_enclosure (bits : UInt64) (shift : Nat) (x : ℝ)
    (hf : Finite bits) (hs : Wasm.IEEE64.sign bits = true) (hx : 0 ≤ x)
    (hn : shift = 0 ∨ 2^52*2^shift ≤ Wasm.IEEE64.scaledMagnitude bits)
    (he : |(Wasm.IEEE64.scaledMagnitude bits : ℝ)-x| ≤ (2:ℝ)^shift/2) :
    value (nextDown bits) ≤ -x/(2:ℝ)^1074 ∧ -x/(2:ℝ)^1074 ≤ value (nextUp bits) := by
  have hb := finite_word_bound bits hf
  have hnraw := bits.toNat_lt
  have hsign : 2^63 ≤ bits.toNat := by
    simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hs
  have hm : Wasm.IEEE64.scaledMagnitude bits = unsignedScaled (bits.toNat-2^63) := by
    rw [scaledMagnitude_abs, absBits_toNat, show bits.toNat%2^63 = bits.toNat-2^63 by omega]
  rw [hm] at hn he
  obtain ⟨hl, hu⟩ := magnitude_enclosure (bits.toNat-2^63) shift x hx hn he
  have hp := word_succ_nat bits (by omega)
  have hw : ¬bits < 0x8000000000000000 := by
    intro hw
    exact (Nat.not_lt.mpr hsign) (UInt64.lt_iff_toNat_lt.mp hw)
  constructor
  · have hz : bits ≠ 0 := by
      intro hz
      subst bits
      contradiction
    simp only [nextDown, hz, ite_false, hw]
    rw [negative_word_value (bits+1) (by omega), hp,
      show bits.toNat+1-2^63 = bits.toNat-2^63+1 by omega]
    exact div_le_div_of_nonneg_right (neg_le_neg hu) (by positivity)
  · by_cases hz : bits = 0x8000000000000000
    · subst bits
      rw [zero_endpoints.2.1, unsigned_word_value 1 (by decide),
        show unsignedScaled (1:UInt64).toNat = 1 by decide +kernel]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · have hne : bits.toNat ≠ 2^63 := fun h => hz (UInt64.toNat_inj.mp h)
      have hpred := word_pred_nat bits (by omega)
      simp only [nextUp, hz, ite_false, hw]
      rw [negative_word_value (bits-1) (by omega), hpred,
        show bits.toNat-1-2^63 = bits.toNat-2^63-1 by omega]
      have hlo : (unsignedScaled (bits.toNat-2^63-1) : ℝ) ≤ x := by
        simpa only [show bits.toNat-2^63 ≠ 0 by omega, ite_false] using hl
      exact div_le_div_of_nonneg_right (neg_le_neg hlo) (by positivity)

theorem enclosure_of_magnitude (bits : UInt64) (shift : Nat) (x : ℝ)
    (hf : Finite bits) (hx : 0 ≤ x)
    (hn : shift = 0 ∨ 2^52*2^shift ≤ Wasm.IEEE64.scaledMagnitude bits)
    (he : |(Wasm.IEEE64.scaledMagnitude bits : ℝ)-x| ≤ (2:ℝ)^shift/2) :
    let exactValue := (if Wasm.IEEE64.sign bits then -x else x)/(2:ℝ)^1074
    value (nextDown bits) ≤ exactValue ∧ exactValue ≤ value (nextUp bits) := by
  cases hs : Wasm.IEEE64.sign bits
  · simpa only [hs, Bool.false_eq_true, ite_false] using
      nonnegative_enclosure bits shift x hf hs hx hn he
  · simpa only [hs, ite_true] using negative_enclosure bits shift x hf hs hx hn he

#print axioms nonnegative_enclosure
#print axioms negative_enclosure
#print axioms enclosure_of_magnitude
end Project.ProofKit.F64Adjacent
