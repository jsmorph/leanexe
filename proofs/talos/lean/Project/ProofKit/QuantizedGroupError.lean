import Project.ProofKit.QuantizedDot
import Project.ProofKit.QuantizedRescaleError
import Project.ProofKit.QuantizationError

namespace Project.ProofKit.QuantizedGroupError
open LeanExe.Models.Gpt2.Quantized LeanExe.Signed32 CodeLib.IEEE32

noncomputable def byteValue (bytes : ByteArray) (index : Nat) : ℝ :=
  decode (extend8Bits bytes[index]!.toUInt32)

theorem scaled_dot (weights input : ByteArray) (weightOffset inputOffset count : Nat)
    (inputScale weightScale : ℝ) (hCount : count ≤ 3072)
    (hInput : ∀ i < count, input[inputOffset + i]! ≠ 128)
    (hWeights : ∀ i < count, weights[weightOffset + i]! ≠ 128) :
    (decode (dot weights input weightOffset inputOffset count) : ℝ) * inputScale * weightScale =
      ∑ i ∈ Finset.range count,
        (inputScale * byteValue input (inputOffset + i)) * (weightScale * byteValue weights (weightOffset + i)) := by
  rw [QuantizedDot.dot_exact weights input weightOffset inputOffset count hCount hInput hWeights]
  simp only [QuantizedInt32.sumPrefix, Int.cast_sum, Int.cast_mul, Finset.sum_mul, byteValue]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem reconstruction (weights input : ByteArray) (weightOffset inputOffset count : Nat)
    (inputScale weightScale : UInt32) (referenceInput referenceWeight inputError weightError : Nat → ℝ)
    (scaleBound outputBound : Nat) (hCount : count ≤ 64)
    (hInput : ∀ i < count, input[inputOffset + i]! ≠ 128)
    (hWeights : ∀ i < count, weights[weightOffset + i]! ≠ 128)
    (hInputError : ∀ i < count,
      |value inputScale * byteValue input (inputOffset + i) - referenceInput i| ≤ inputError i)
    (hWeightError : ∀ i < count,
      |value weightScale * byteValue weights (weightOffset + i) - referenceWeight i| ≤ weightError i)
    (hInputScale : Finite inputScale) (hWeightScale : Finite weightScale)
    (hScaleLower : 173 ≤ scaleBound) (hScaleUpper : scaleBound ≤ 425)
    (hOutputLower : 173 ≤ outputBound) (hOutputUpper : outputBound ≤ 425)
    (hScaleProduct : Wasm.IEEE32.scaledMagnitude inputScale * Wasm.IEEE32.scaledMagnitude weightScale < 2 ^ scaleBound)
    (hOutputProduct : Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits
        (dot weights input weightOffset inputOffset count)) *
      Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.mulBits inputScale weightScale) < 2 ^ outputBound) :
    let accumulator := dot weights input weightOffset inputOffset count
    Finite (rescale accumulator inputScale weightScale) ∧
      |value (rescale accumulator inputScale weightScale) -
          ∑ i ∈ Finset.range count, referenceInput i * referenceWeight i| ≤
        F32MultiplicationBounds.epsilon outputBound +
        |(decode accumulator : ℝ)| * F32MultiplicationBounds.epsilon scaleBound +
        ∑ i ∈ Finset.range count, (|referenceWeight i| * inputError i +
          |referenceInput i| * weightError i + inputError i * weightError i) := by
  dsimp only
  have hRange := QuantizedDot.dot_prefix_range weights input weightOffset inputOffset count (by omega) hInput hWeights
  have hCountInt : (count : Int) ≤ 64 := by exact_mod_cast hCount
  have hIntegerBound : |decode (dot weights input weightOffset inputOffset count)| ≤ 1032256 := by omega
  have hNaturalBound : (decode (dot weights input weightOffset inputOffset count)).natAbs ≤ 1032256 := by
    rw [← Int.natCast_natAbs] at hIntegerBound
    exact_mod_cast hIntegerBound
  have hAbs : (decode (dot weights input weightOffset inputOffset count)).natAbs < 2 ^ 24 := by
    omega
  have hRescale := QuantizedRescaleError.rescale_error _ inputScale weightScale scaleBound outputBound
    hAbs hInputScale hWeightScale hScaleLower hScaleUpper hOutputLower hOutputUpper hScaleProduct hOutputProduct
  have hDot := QuantizationError.dot_error (Finset.range count) referenceInput referenceWeight
    (fun i => value inputScale * byteValue input (inputOffset + i))
    (fun i => value weightScale * byteValue weights (weightOffset + i)) inputError weightError
    (fun i hi => hInputError i (Finset.mem_range.mp hi))
    (fun i hi => hWeightError i (Finset.mem_range.mp hi))
  rw [← scaled_dot weights input weightOffset inputOffset count (value inputScale) (value weightScale)
    (by omega) hInput hWeights] at hDot
  refine ⟨hRescale.1, ?_⟩
  exact (abs_sub_le _ _ _).trans (add_le_add hRescale.2 hDot)

#print axioms scaled_dot
#print axioms reconstruction
end Project.ProofKit.QuantizedGroupError
