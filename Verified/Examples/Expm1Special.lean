import Verified.Examples.Expm1Theorem

/-!
The exceptional results of `Tanh.expm1`: both zeros return themselves, positive infinity returns
positive infinity, negative infinity returns `-1`, and a NaN returns the canonical NaN.
-/

namespace Verified.Examples.Expm1Special
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches Expm1Theorem

theorem expm1_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Tanh.expm1 x).toBits = x.toBits := by
  have hhw : highWord x.toBits = 0 := by rcases h with h | h <;> rw [h] <;> decide
  have h1 : ¬ highWord x.toBits ≥ 2146435072 := by rw [hhw]; decide
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    rw [hhw]; exact fun h => absurd h.1 (by decide)
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    rw [hhw]; exact fun h => absurd h.1 (by decide)
  have h4 : ¬ highWord x.toBits > 1071001154 := by rw [hhw]; decide
  have h5 : highWord x.toBits < 1016070144 := by rw [hhw]; decide
  rw [select_tiny x h1 h2 h3 h4 h5]
  simp only [F64Bits.toBits_sub, F64Bits.toBits_add, Expm1Words.float_ofBits, huge_bits]
  rcases h with h | h <;> rw [h] <;> decide +kernel

theorem expm1_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Tanh.expm1 x).toBits = 0x7FF0000000000000 := by
  have hc : (x.toBits &&& 4503599627370495 != 0) = false := by rw [h]; decide
  have hs : sgn x.toBits = false := by rw [h]; decide
  rw [select_nonfinite x (by rw [h]; decide), hc, hs]
  simp only [Bool.false_eq_true, ite_false]
  exact h

theorem expm1_neg_infinity (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Tanh.expm1 x).toBits = 0xBFF0000000000000 := by
  have hc : (x.toBits &&& 4503599627370495 != 0) = false := by rw [h]; decide
  have hs : sgn x.toBits = true := by rw [h]; decide
  rw [select_nonfinite x (by rw [h]; decide), hc, hs]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [F64Bits.toBits_neg]
  decide +kernel

theorem expm1_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Tanh.expm1 x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hn := h
  simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hn
  have h1 : highWord x.toBits ≥ 2146435072 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [highWord_toNat]
    change 2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32
    have : x.toBits.toNat % 2 ^ 63 / 2 ^ 52 = x.toBits.toNat / 2 ^ 52 % 2 ^ 11 := by
      rw [show (2 : Nat) ^ 63 = 2 ^ 52 * 2 ^ 11 by norm_num, Nat.mod_mul_right_div_self]
    omega
  have hf : (x.toBits &&& 4503599627370495 != 0) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro h0
    have h0' := congrArg UInt64.toNat h0
    rw [UInt64.toNat_and] at h0'
    change x.toBits.toNat &&& (2 ^ 52 - 1) = 0 at h0'
    rw [Nat.and_two_pow_sub_one_eq_mod] at h0'
    exact hn.2 h0'
  rw [select_nonfinite x h1, ite_eq_left hf, F64Bits.toBits_add]
  simp [Wasm.IEEE64.add, h]

#print axioms expm1_zero
#print axioms expm1_pos_infinity
#print axioms expm1_neg_infinity
#print axioms expm1_nan

end Verified.Examples.Expm1Special
