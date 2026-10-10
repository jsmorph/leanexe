import Verified.Examples.LogCoreStep
import Verified.Examples.LogBranches

/-!
`Log.log` on positive normal arguments outside the path near 1, `[15/16, 1 + 265/4096)`: the result
lies within one representable step of the nearest-even reference of `log x`.  These arguments take
`Log.logCore` with the argument's own bits, so `LogCoreStep.core_within` applies with `E` the
exponent field and `f` the fraction field.
-/

namespace Verified.Examples.LogMain
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem bound_values :
    value (0x3FEE000000000000 : UInt64) = 15 / 16 ∧
      value (0x3FF1090000000000 : UInt64) = 1 + 265 / 4096 := by
  have h1 : PolyBound.ratOfWord 0x3FEE000000000000 = 15 / 16 := by decide +kernel
  have h2 : PolyBound.ratOfWord 0x3FF1090000000000 = 1 + 265 / 4096 := by decide +kernel
  rw [← PolyBound.ratOfWord_cast, ← PolyBound.ratOfWord_cast, h1, h2]
  norm_num

/-- The value of a positive normal word in the form of `LogCoreStep.core_within`. -/
theorem normal_form (w : UInt64) (hs : Wasm.IEEE64.sign w = false)
    (he : 1 ≤ Wasm.IEEE64.exponent w) :
    value w = ((2 : ℝ) ^ 52 + Wasm.IEEE64.fraction w) *
      (2 : ℝ) ^ ((Wasm.IEEE64.exponent w : Int) - 1075) := by
  rw [F64Magnitude.normal_value w hs (by omega), mul_div_assoc]
  congr 1
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

/-- `Log.log` on a positive normal argument outside the path near 1. -/
theorem log_normal_within (x : Float) (hf : Finite x.toBits)
    (hs : Wasm.IEEE64.sign x.toBits = false) (he : 1 ≤ Wasm.IEEE64.exponent x.toBits)
    (hnear : x.toBits.toNat < 4606619468846596096 ∨ 4607473789381378048 ≤ x.toBits.toNat) :
    F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits)) (Log.log x).toBits := by
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hfin : Wasm.IEEE64.exponent x.toBits ≠ 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    exact hf
  have hN : x.toBits.toNat = Wasm.IEEE64.exponent x.toBits * 4503599627370496 +
      Wasm.IEEE64.fraction x.toBits := by
    simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Nat.reducePow] at he hfin ⊢
    simp only [Nat.reducePow] at hlt
    omega
  have hfrac : Wasm.IEEE64.fraction x.toBits < 4503599627370496 := by
    simp only [Wasm.IEEE64.fraction]
    omega
  have hlo : 4503599627370496 ≤ x.toBits.toNat := by omega
  have hhi : x.toBits.toNat < 9218868437227405312 := by
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    simp only [Nat.reducePow] at hlt
    omega
  rw [Log.log, LogBranches.normal_selected _ _ x hlo hhi hnear, normal_form _ hs he]
  have hv := normal_form _ hs he
  obtain ⟨hb1, hb2⟩ := bound_values
  apply LogCoreStep.core_within x.toBits (Wasm.IEEE64.exponent x.toBits)
    (Wasm.IEEE64.fraction x.toBits) (by omega) (by omega) hfrac
  · have : x.toBits.toNat < 18446744073709551616 := by omega
    rw [hN]
    push_cast
    omega
  · rw [← hv]
    rcases hnear with h | h
    · left
      have := F64PositiveOrder.value_strict (left := x.toBits)
        (right := (0x3FEE000000000000 : UInt64)) (by decide) h
      rw [hb1] at this
      exact this.le
    · right
      have := (F64PositiveOrder.value_le_iff (left := (0x3FF1090000000000 : UInt64))
        (right := x.toBits) (by decide) hlt).mpr h
      rw [hb2] at this
      exact this

#print axioms bound_values
#print axioms normal_form
#print axioms log_normal_within

end Verified.Examples.LogMain
