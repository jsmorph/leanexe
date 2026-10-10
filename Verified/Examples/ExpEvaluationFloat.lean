import LeanExe.ProofKit.F64Bits
import Verified.Examples.ExpEvaluationBounds

namespace Verified.Examples.ExpEvaluationBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def floatEvaluation (r t : Float) : Float :=
  let r2 := r * r
  t + r + r2 * (Float.ofBits 0x3FDFFFFFFFFFFDBD + r * Float.ofBits 0x3FC555555555543C) +
    r2 * r2 * (Float.ofBits 0x3FA55555CF172B91 + r * Float.ofBits 0x3F81111167A4D017)

theorem evaluation_bits (r t : Float) :
    (floatEvaluation r t).toBits = evaluation r.toBits t.toBits := by
  obtain ⟨h2, h3, h4, h5⟩ := coefficient_finite
  simp [floatEvaluation, evaluation, LeanExe.ProofKit.F64Bits.toBits_add,
    LeanExe.ProofKit.F64Bits.toBits_mul, LeanExe.ProofKit.F64Bits.toBits_ofBits,
    not_nan_of_finite h2, not_nan_of_finite h3, not_nan_of_finite h4, not_nan_of_finite h5]

#print axioms evaluation_bits

end Verified.Examples.ExpEvaluationBounds
