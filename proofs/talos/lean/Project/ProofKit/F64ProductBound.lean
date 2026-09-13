import Project.ProofKit.F64MulBounds
import Project.ProofKit.F64Maximum

namespace Project.ProofKit.F64ProductBound
open CodeLib.IEEE64
open F64Order

set_option exponentiation.threshold 4096

theorem product_le_of_rounded_half (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hpos : 0 ≤ value a * value b) (hmax : |value a * value b| < (2 : ℝ)^1022)
    (hc : positiveBits (Wasm.IEEE64.mul a b) = true)
    (hhalf : Wasm.IEEE64.mul a b ≤ 0x3FE0000000000000) :
    value a * value b ≤ 51 / 100 := by
  have halfPositive : positiveBits 0x3FE0000000000000 = true := by decide
  have halfValue : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have hupper := positive_value_le (Wasm.IEEE64.mul a b) 0x3FE0000000000000 hc halfPositive hhalf
  rw [halfValue] at hupper
  have herr := (F64MulBounds.mul_real_mixed a b ha hb hmax).2
  rw [abs_of_nonneg hpos] at herr
  have hlo := (abs_le.mp herr).1
  have hu : unitRoundoff64 ≤ (1 : ℝ) / 1000 := by norm_num [unitRoundoff64]
  have heta : multiplicationUnderflowEpsilon ≤ (1 : ℝ) / 1000 := by
    norm_num [multiplicationUnderflowEpsilon]
  have hscaled := mul_le_mul_of_nonneg_right hu hpos
  linarith only [hupper, hlo, hscaled, heta]

#print axioms product_le_of_rounded_half
end Project.ProofKit.F64ProductBound
