import Verified.Examples.Sinh
import Verified.Examples.ExpTightFloat
import Verified.Examples.TanhWords

/-!
Words and real facts for the proofs about `Sinh.sinh` and `Sinh.cosh`: the word of `0.5`, exact
halving of a normal word (`mul_half`), the absolute value of a Float, and the lower bound
`exp a ≥ 1.4142` above the threshold `0.34657359` of `cosh`.
-/

namespace Verified.Examples.SinhWords
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem half_bits : (0.5 : Float).toBits = Expm1Words.half := rfl

theorem half_eq : Expm1Words.half = Wasm.IEEE64.encodeFinite false 1022 0 := by decide

theorem half_value : value Expm1Words.half = 1 / 2 := by
  have h : Wasm.IEEE64.scaledValue Expm1Words.half = (2 : Int) ^ 1073 := by decide +kernel
  rw [value, h]
  norm_num

theorem half_finite : Finite Expm1Words.half := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem half_sign : Wasm.IEEE64.sign Expm1Words.half = false := by decide +kernel

/-- Halving a word of value at least `2 ^ -1021` is exact. -/
theorem mul_half (a : UInt64) (haf : Finite a) (ha : 1 / 2 ^ 1021 ≤ value a) :
    Finite (Wasm.IEEE64.mul Expm1Words.half a) ∧
      value (Wasm.IEEE64.mul Expm1Words.half a) = value a / 2 := by
  have he := F64Magnitude.exponent_ge_of_value a 2 (by norm_num) (by
    rw [show ((2 : Nat) : Int) - 1023 = -1021 by norm_num, zpow_neg, zpow_ofNat, ← one_div]
    exact ha)
  have hlt : Wasm.IEEE64.exponent a < 2048 := Nat.mod_lt _ (by norm_num)
  rw [half_eq]
  obtain ⟨hf, hv⟩ := F64PowerScale.mul_power_finite 1022 a (by norm_num) (by norm_num) haf
    (by omega) (by omega) (by omega)
  refine ⟨hf, ?_⟩
  rw [hv, show ((1022 : Nat) : Int) - 1023 = -1 by norm_num, zpow_neg_one]
  ring

theorem abs_float (x : Float) (hxf : Finite x.toBits) :
    Finite x.abs.toBits ∧ value x.abs.toBits = |value x.toBits| := by
  rw [F64Bits.toBits_abs]
  exact ⟨TanhWords.abs_finite _ hxf, TanhWords.abs_value _⟩

/-- `exp a ≥ 1.4142` for `a ≥ 0.34657359`, from `exp (2 a) ≥ 2 exp (-10 ^ -9)`. -/
theorem exp_lower (A : ℝ) (hA : 34657359 / 10 ^ 8 ≤ A) : 14142 / 10000 ≤ Real.exp A := by
  have hl := ExpTight.log_two_bounds.2
  have h1 : Real.exp (Real.log 2 + -(1 / 10 ^ 9)) ≤ Real.exp (A + A) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_add, Real.exp_add, Real.exp_log two_pos] at h1
  have h2 := Real.add_one_le_exp (-(1 / 10 ^ 9 : ℝ))
  nlinarith [Real.exp_pos A]

theorem cosh_exp (A : ℝ) : Real.cosh A = (Real.exp A + 1 / Real.exp A) / 2 := by
  rw [Real.cosh_eq, Real.exp_neg, one_div]

theorem sinh_exp (A : ℝ) : Real.sinh A = (Real.exp A - 1 / Real.exp A) / 2 := by
  rw [Real.sinh_eq, Real.exp_neg, one_div]

#print axioms mul_half
#print axioms exp_lower

end Verified.Examples.SinhWords
