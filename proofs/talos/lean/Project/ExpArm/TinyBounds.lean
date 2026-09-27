import Project.ExpArm.SpecialValues
import Project.ProofKit.F64StrictOrder
import Mathlib.Analysis.Complex.Exponential

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem one_value : value 0x3FF0000000000000 = 1 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem tiny_limit_value : value 0x3C90000000000000 = 1 / (2 : ℝ)^54 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem tiny_error (x : UInt64)
    (hx : x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000) :
    Finite x ∧ Finite (exp x) ∧
      |value (exp x) - Real.exp (value x)| < 1 / (2 : ℝ)^53 := by
  have hf : Finite x := (finiteBits_iff x).mp (by
    simp only [finiteBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
      absBits] at *
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega)
  have hm : |value x| < 1 / (2 : ℝ)^54 := by
    have h := abs_value_lt x 0x3C90000000000000 hx
    simpa only [tiny_limit_value, abs_of_pos (by positivity : 0 < 1 / (2 : ℝ)^54)] using h
  rw [exp_tiny x hx]
  refine ⟨hf, by rfl, ?_⟩
  rw [one_value, abs_sub_comm]
  have h := Real.abs_exp_sub_one_le (hm.le.trans (by norm_num))
  calc
    _ ≤ 2 * |value x| := h
    _ < 2 * (1 / (2 : ℝ)^54) := mul_lt_mul_of_pos_left hm (by norm_num)
    _ = 1 / (2 : ℝ)^53 := by norm_num

#print axioms tiny_error
end Project.ExpArm
