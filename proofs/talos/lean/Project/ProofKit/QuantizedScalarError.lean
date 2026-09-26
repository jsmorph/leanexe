import Project.ProofKit.QuantizedClipping
import Project.ProofKit.F32DivisionBounds
import Project.ProofKit.F32Div

namespace Project.ProofKit.QuantizedScalarError
open CodeLib.IEEE32

theorem reconstruction (input scale : UInt32) (bound : Nat)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 275)
    (hInput : CodeLib.IEEE32.Finite input) (hScaleFinite : CodeLib.IEEE32.Finite scale)
    (hScale : 0 < value scale) (hNonzero : Wasm.IEEE32.scaledMagnitude scale ≠ 0)
    (hQuotient : Wasm.IEEE32.scaledMagnitude input * 2 ^ 149 ≤
      Wasm.IEEE32.scaledMagnitude scale * 2 ^ bound) :
    |value scale * (QuantizedError.coefficient input scale : ℝ) - value input| ≤
      value scale * (1 / 2 + max 0 (|value (LeanExe.Float32.divBits input scale)| - 127) +
        F32DivisionBounds.epsilon bound) := by
  apply QuantizedError.reconstruction_error input scale _ _ hScale
  · rw [F32Div.div_eq]
    exact (F32DivisionBounds.div_real_error input scale bound hLower hUpper hInput
      hScaleFinite hNonzero hQuotient).2
  · exact (QuantizedClipping.error (LeanExe.Float32.divBits input scale)).le

#print axioms reconstruction
end Project.ProofKit.QuantizedScalarError
