import Verified.Examples.Erf
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64Sign
import LeanExe.ProofKit.F64PositiveOrder

/-!
The paths of `Erf.erfWith` by the value of the argument.  The code compares the
high word of `|x|`, `ix = (bits >>> 32) &&& 0x7fffffff`, with constants whose low words are zero, so
`ix < T` holds exactly when the magnitude of `x` is below the double with high word `T`
(`ix_lt_iff`).  Each threshold's value is computed from its bits.
-/

namespace Verified.Examples.ErfBranches
open CodeLib.IEEE64 LeanExe.ProofKit F64Magnitude F64PositiveOrder

set_option exponentiation.threshold 4096

/-- The high word of the magnitude, as the code computes it. -/
def ix (b : UInt64) : UInt64 := (b >>> 32) &&& 0x7fffffff

theorem ix_toNat (b : UInt64) : (ix b).toNat = b.toNat % 2 ^ 63 / 2 ^ 32 := by
  have hb := b.toNat_lt
  rw [ix, UInt64.toNat_and, UInt64.toNat_shiftRight]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  rw [show (2147483647 : Nat) = 2 ^ 31 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `ix < T` compares the magnitude's bits with `T · 2^32`. -/
theorem ix_lt_iff (b : UInt64) (T : Nat) (hT : T < 2 ^ 31) :
    ix b < UInt64.ofNat T ↔ b.toNat % 2 ^ 63 < T * 2 ^ 32 := by
  have hsz : UInt64.size = 18446744073709551616 := rfl
  rw [UInt64.lt_iff_toNat_lt, ix_toNat, UInt64.toNat_ofNat_of_lt' (by omega)]
  omega

/-- The magnitude word of `b`. -/
def absWord (b : UInt64) : UInt64 := UInt64.ofNat (b.toNat % 2 ^ 63)

theorem absWord_toNat (b : UInt64) : (absWord b).toNat = b.toNat % 2 ^ 63 := by
  have hsz : UInt64.size = 18446744073709551616 := rfl
  rw [absWord, UInt64.toNat_ofNat_of_lt' (by have := Nat.mod_lt b.toNat (by norm_num : 0 < 2 ^ 63); omega)]

theorem absWord_value (b : UInt64) : value (absWord b) = |value b| := by
  have hb := b.toNat_lt
  have ht := absWord_toNat b
  have hs : Wasm.IEEE64.sign (absWord b) = false := by
    simp only [Wasm.IEEE64.sign, ht, decide_eq_false_iff_not, not_le]
    omega
  have he : Wasm.IEEE64.exponent (absWord b) = Wasm.IEEE64.exponent b := by
    simp only [Wasm.IEEE64.exponent, ht]
    omega
  have hf : Wasm.IEEE64.fraction (absWord b) = Wasm.IEEE64.fraction b := by
    simp only [Wasm.IEEE64.fraction, ht]
    omega
  have hm : Wasm.IEEE64.scaledMagnitude (absWord b) = Wasm.IEEE64.scaledMagnitude b := by
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf]
  simp only [value, Wasm.IEEE64.scaledValue, hs, hm, Bool.false_eq_true, ite_false]
  split
  · rw [Int.cast_neg, neg_div, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    congr 1
    push_cast
    exact (abs_of_nonneg (by positivity)).symm
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    congr 1
    push_cast
    exact (abs_of_nonneg (by positivity)).symm

/-- For a finite argument, `ix < T` holds exactly when `|x|` is below the double with high word
`T`. -/
theorem ix_lt_value (b : UInt64) (T : Nat) (hT : T < 2 ^ 31) :
    ix b < UInt64.ofNat T ↔ |value b| < value (UInt64.ofNat (T * 2 ^ 32)) := by
  have hsz : UInt64.size = 18446744073709551616 := rfl
  rw [ix_lt_iff b T hT, ← absWord_value]
  have hTw : (UInt64.ofNat (T * 2 ^ 32)).toNat = T * 2 ^ 32 :=
    UInt64.toNat_ofNat_of_lt' (by
      have : T * 2 ^ 32 < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hT (by positivity)
      omega)
  have ha := absWord_toNat b
  have h63a : (absWord b).toNat < 2 ^ 63 := by rw [ha]; exact Nat.mod_lt _ (by norm_num)
  have h63T : (UInt64.ofNat (T * 2 ^ 32)).toNat < 2 ^ 63 := by
    rw [hTw]
    have : T * 2 ^ 32 < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hT (by positivity)
    omega
  constructor
  · intro h
    exact value_strict h63T (by rw [ha, hTw]; exact h)
  · intro h
    by_contra hn
    have hle : (UInt64.ofNat (T * 2 ^ 32)).toNat ≤ (absWord b).toNat := by rw [ha, hTw]; omega
    have := (value_le_iff h63T h63a).mpr hle
    linarith

#print axioms ix_toNat
#print axioms ix_lt_iff
#print axioms absWord_value
#print axioms ix_lt_value

end Verified.Examples.ErfBranches
