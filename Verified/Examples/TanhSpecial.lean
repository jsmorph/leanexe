import Verified.Examples.TanhMain

/-!
The exceptional results of `Tanh.tanh`: both zeros return themselves, positive infinity returns 1,
negative infinity returns `-1`, and a NaN returns the canonical NaN.
-/

namespace Verified.Examples.TanhSpecial
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches TanhBranches TanhTheorem

theorem tanh_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Tanh.tanh x).toBits = x.toBits := by
  have hhw : highWord x.toBits = 0 := by rcases h with h | h <;> rw [h] <;> decide
  have hxf : Finite x.toBits := by
    rcases h with h | h <;> rw [h] <;> unfold CodeLib.IEEE64.Finite <;> decide
  have hv : value x.toBits = 0 := by
    rcases h with h | h <;> rw [h]
    · exact F64Magnitude.value_zero
    · have : Wasm.IEEE64.scaledValue (0x8000000000000000 : UInt64) = 0 := by decide
      simp [value, this]
  have h1 : ¬ highWord x.toBits ≥ 2146435072 := by rw [hhw]; decide
  rw [select_tiny x h1 (by rw [hhw]; decide) (huge_add_gt x hxf (by rw [hv]; norm_num))]

theorem tanh_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Tanh.tanh x).toBits = 0x3FF0000000000000 := by
  have hs : sgn x.toBits = false := by rw [h]; decide
  rw [TanhBranches.select_nonfinite x (by rw [h]; decide), hs]
  simp only [Bool.false_eq_true, ite_false]
  rw [F64Bits.toBits_add, F64Bits.toBits_div, h, one_bits]
  decide +kernel

theorem tanh_neg_infinity (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Tanh.tanh x).toBits = 0xBFF0000000000000 := by
  have hs : sgn x.toBits = true := by rw [h]; decide
  rw [TanhBranches.select_nonfinite x (by rw [h]; decide), hs]
  simp only [ite_true]
  rw [F64Bits.toBits_sub, F64Bits.toBits_div, h, one_bits]
  decide +kernel

theorem tanh_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Tanh.tanh x).toBits = Wasm.IEEE64.canonicalNaN := by
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
  have hd : Wasm.IEEE64.div Expm1Words.one x.toBits = Wasm.IEEE64.canonicalNaN := by
    simp [Wasm.IEEE64.div, h]
  rw [TanhBranches.select_nonfinite x h1]
  cases sgn x.toBits
  · simp only [Bool.false_eq_true, ite_false]
    rw [F64Bits.toBits_add, F64Bits.toBits_div, one_bits, hd]
    decide +kernel
  · simp only [ite_true]
    rw [F64Bits.toBits_sub, F64Bits.toBits_div, one_bits, hd]
    decide +kernel

#print axioms tanh_zero
#print axioms tanh_pos_infinity
#print axioms tanh_neg_infinity
#print axioms tanh_nan

end Verified.Examples.TanhSpecial
