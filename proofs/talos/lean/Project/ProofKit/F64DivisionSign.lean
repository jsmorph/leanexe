import Project.ProofKit.F64DivBounds
import Mathlib.Tactic

namespace Project.ProofKit.F64DivBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem div_sign (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hbound : |value a/value b| < (2:ℝ)^1022) :
    Wasm.IEEE64.sign (Wasm.IEEE64.div a b) = (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
  have hbMagPos : (0:ℝ) < Wasm.IEEE64.scaledMagnitude b := by
    exact_mod_cast Nat.pos_of_ne_zero hb0
  have hscaled : Wasm.IEEE64.scaledMagnitude a*2^1074 <
      Wasm.IEEE64.scaledMagnitude b*2^2096 := by
    rw [quotient_abs_scaled] at hbound
    have hh := (div_lt_iff₀ hbMagPos).mp hbound
    have hm := mul_lt_mul_of_pos_right hh (by positivity : (0:ℝ) < (2:ℝ)^1074)
    have hid : (2:ℝ)^1022*Wasm.IEEE64.scaledMagnitude b*(2:ℝ)^1074 =
        Wasm.IEEE64.scaledMagnitude b*(2:ℝ)^2096 := by
      rw [mul_comm ((2:ℝ)^1022), mul_assoc, ← pow_add]
    rw [hid] at hm
    exact_mod_cast hm
  rw [div_finite_rounder a b ha hb hb0]
  exact (F64RationalBounds.rational_relative _ _ _ hb0 hscaled).2.1

theorem div_zero_value (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0) (hz : value a = 0) :
    value (Wasm.IEEE64.div a b) = 0 := by
  have hmag : Wasm.IEEE64.scaledMagnitude a = 0 := by
    have hh : |(Wasm.IEEE64.scaledValue a : ℝ)| = 0 := by
      have hv : (Wasm.IEEE64.scaledValue a : ℝ) = 0 := by
        simpa only [value, div_eq_zero_iff, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
          false_and, or_false] using hz
      rw [hv, abs_zero]
    rw [abs_scaledValue_real] at hh
    exact_mod_cast hh
  rw [div_finite_rounder a b ha hb hb0, hmag, zero_mul]
  cases hs : (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) <;>
    norm_num [Wasm.IEEE64.roundRationalMagnitude, Wasm.IEEE64.signMask, value,
      Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
      Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem sign_false_of_value_pos (word : UInt64) (hp : 0 < value word) :
    Wasm.IEEE64.sign word = false := by
  cases hs : Wasm.IEEE64.sign word
  · rfl
  · have hn : value word ≤ 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)
    linarith

theorem div_nonnegative (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (han : 0 ≤ value a) (hbp : 0 < value b)
    (hbound : |value a/value b| < (2:ℝ)^1022) :
    0 ≤ value (Wasm.IEEE64.div a b) := by
  have hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    intro hh
    simp [value, Wasm.IEEE64.scaledValue, hh] at hbp
  by_cases hz : value a = 0
  · rw [div_zero_value a b ha hb hb0 hz]
  · have hap : 0 < value a := lt_of_le_of_ne han (Ne.symm hz)
    have hs := div_sign a b ha hb hb0 hbound
    rw [sign_false_of_value_pos a hap, sign_false_of_value_pos b hbp] at hs
    simp only [bne_self_eq_false] at hs
    simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false, Int.cast_natCast]
    positivity

#print axioms div_sign
#print axioms div_nonnegative
end Project.ProofKit.F64DivBounds
