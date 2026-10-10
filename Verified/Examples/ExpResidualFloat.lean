import Verified.Examples.ExpResidualBounds

namespace Verified.Examples.ExpResidualBounds
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def floatResidual (x : Float) : Float :=
  let kd := ExpReductionSelection.floatInteger x
  x + kd * Float.ofBits 0xBF762E42FEFA0000 + kd * Float.ofBits 0xBD0CF79ABC9E3B3A

theorem residual_bits (x : Float) : (floatResidual x).toBits = residual x.toBits := by
  have hh := ExpReductionBounds.reduction_constants_finite.2.2.1
  have hl := ExpReductionBounds.reduction_constants_finite.2.2.2
  simp [floatResidual, residual, ExpHighResidual.highResidual, ExpHighResidual.highProduct,
    lowProduct, F64Bits.toBits_add, F64Bits.toBits_mul, ExpReductionSelection.floatInteger_bits,
    F64Bits.toBits_ofBits, not_nan_of_finite hh, not_nan_of_finite hl]

theorem floatResidual_bounds (x : Float) (hxf : Finite x.toBits)
    (hx : |value x.toBits| ≤ 768) :
    Finite (floatResidual x).toBits ∧ |value (floatResidual x).toBits| ≤ 1 / 256 ∧
      |value (floatResidual x).toBits - ideal x.toBits| ≤ 1 / (2 : ℝ) ^ 60 := by
  rw [residual_bits]
  exact residual_bounds x.toBits hxf hx

#print axioms residual_bits
#print axioms floatResidual_bounds

end Verified.Examples.ExpResidualBounds
