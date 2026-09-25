import Project.ProofKit.F32IntegerExact
import Project.ProofKit.F32MultiplicationBounds
import Project.ProofKit.F32Mul
import LeanExe.Models.Gpt2.Quantized.Kernel

namespace Project.ProofKit.QuantizedRescaleError
open CodeLib.IEEE32 LeanExe.Models.Gpt2.Quantized

theorem rescale_error (accumulator inputScale weightScale : UInt32)
    (scaleBound outputBound : Nat)
    (hAccumulator : (LeanExe.Signed32.decode accumulator).natAbs < 2 ^ 24)
    (hInput : CodeLib.IEEE32.Finite inputScale)
    (hWeight : CodeLib.IEEE32.Finite weightScale)
    (hScaleLower : 173 ≤ scaleBound) (hScaleUpper : scaleBound ≤ 425)
    (hOutputLower : 173 ≤ outputBound) (hOutputUpper : outputBound ≤ 425)
    (hScaleProduct : Wasm.IEEE32.scaledMagnitude inputScale *
      Wasm.IEEE32.scaledMagnitude weightScale < 2 ^ scaleBound)
    (hOutputProduct : Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits accumulator) *
      Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.mulBits inputScale weightScale) < 2 ^ outputBound) :
    CodeLib.IEEE32.Finite (rescale accumulator inputScale weightScale) ∧
      |value (rescale accumulator inputScale weightScale) -
        (LeanExe.Signed32.decode accumulator : ℝ) * value inputScale * value weightScale| ≤
        F32MultiplicationBounds.epsilon outputBound +
          |(LeanExe.Signed32.decode accumulator : ℝ)| * F32MultiplicationBounds.epsilon scaleBound := by
  have hInteger := F32IntegerExact.conversion_exact accumulator hAccumulator
  have hScale := F32MultiplicationBounds.mul_real_error inputScale weightScale scaleBound
    hScaleLower hScaleUpper hInput hWeight hScaleProduct
  rw [← F32Mul.mul_eq] at hScale
  have hOutput := F32MultiplicationBounds.mul_real_error
    (LeanExe.Float32.ofInt32Bits accumulator) (LeanExe.Float32.mulBits inputScale weightScale)
    outputBound hOutputLower hOutputUpper hInteger.1 hScale.1 hOutputProduct
  rw [← F32Mul.mul_eq, hInteger.2] at hOutput
  refine ⟨hOutput.1, ?_⟩
  calc
    |value (rescale accumulator inputScale weightScale) -
        (LeanExe.Signed32.decode accumulator : ℝ) * value inputScale * value weightScale| =
      |(value (rescale accumulator inputScale weightScale) -
          (LeanExe.Signed32.decode accumulator : ℝ) * value (LeanExe.Float32.mulBits inputScale weightScale)) +
        (LeanExe.Signed32.decode accumulator : ℝ) *
          (value (LeanExe.Float32.mulBits inputScale weightScale) - value inputScale * value weightScale)| := by
        congr 1
        ring
    _ ≤ |value (rescale accumulator inputScale weightScale) -
          (LeanExe.Signed32.decode accumulator : ℝ) * value (LeanExe.Float32.mulBits inputScale weightScale)| +
        |(LeanExe.Signed32.decode accumulator : ℝ)| *
          |value (LeanExe.Float32.mulBits inputScale weightScale) - value inputScale * value weightScale| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ _ := add_le_add hOutput.2
      (mul_le_mul_of_nonneg_left hScale.2 (abs_nonneg _))

#print axioms rescale_error
end Project.ProofKit.QuantizedRescaleError
