import Project.Gpt2CachedStep.LayerNorm.Source
import Project.Gpt2RowInvStd.DenominatorError

namespace Project.Gpt2CachedStep.LayerNorm.Numerical
open LeanExe.Models.Gpt2 Project.ProofKit

theorem word_generate (count : Nat) (f : Nat → UInt32) (i : Nat) (hi : i < count) :
    word (LeanExe.Packed.generateUInt32LE count f) i = f i := by
  unfold word
  rw [Nat.mul_comm i 4]
  exact PackedSource.generate_read count f i hi

def centered (input : ByteArray) (i : Nat) : UInt32 :=
  LeanExe.Float32.subBits (word input i) (rowMean input 0)

def inverse (input : ByteArray) : UInt32 := rowInvStd input 0 (rowMean input 0)

def normalized (input : ByteArray) (i : Nat) : UInt32 :=
  LeanExe.Float32.mulBits (centered input i) (inverse input)

def scaled (weights input : ByteArray) (scaleOffset i : Nat) : UInt32 :=
  LeanExe.Float32.mulBits (normalized input i) (word weights (scaleOffset + i))

theorem component_source (weights input : ByteArray) (scaleOffset biasOffset i : Nat) (hi : i < 768) :
    word (layerNorm weights input scaleOffset biasOffset 1) i =
      LeanExe.Float32.addBits (scaled weights input scaleOffset i) (word weights (biasOffset + i)) := by
  rw [layerNorm_eq, word_generate _ _ i (by simpa using hi)]
  simp only [value, means, inverses, Nat.one_mul, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  rw [word_generate 1 (rowMean input) 0 (by decide)]
  rw [word_generate 1 _ 0 (by decide)]
  simp only [means, word_generate 1 (rowMean input) 0 (by decide)]
  simp only [scaled, normalized, centered, inverse, F32Add.add_eq, F32Mul.mul_eq, F32Sub.sub_eq]

noncomputable def componentError (center inverse gain centerError inverseError : ℝ)
    (normBound scaleBound addBound : Nat) : ℝ :=
  F32AdditionBounds.epsilon addBound +
    (F32MultiplicationBounds.epsilon scaleBound +
      (F32MultiplicationBounds.epsilon normBound + (|center| * inverseError + centerError * |inverse|)) * |gain|)

theorem component_error (weights input : ByteArray) (scaleOffset biasOffset i : Nat) (hi : i < 768)
    (C I centerError inverseError : ℝ) (normBound scaleBound addBound : Nat)
    (hCenter : CodeLib.IEEE32.Finite (centered input i))
    (hInverse : CodeLib.IEEE32.Finite (inverse input))
    (hScale : CodeLib.IEEE32.Finite (word weights (scaleOffset + i)))
    (hBias : CodeLib.IEEE32.Finite (word weights (biasOffset + i)))
    (hCenterError : |CodeLib.IEEE32.value (centered input i) - C| ≤ centerError)
    (hInverseError : |CodeLib.IEEE32.value (inverse input) - I| ≤ inverseError)
    (hNormLower : 173 ≤ normBound) (hNormUpper : normBound ≤ 425)
    (hNormRange : Wasm.IEEE32.scaledMagnitude (centered input i) * Wasm.IEEE32.scaledMagnitude (inverse input) < 2 ^ normBound)
    (hScaleLower : 173 ≤ scaleBound) (hScaleUpper : scaleBound ≤ 425)
    (hScaleRange : Wasm.IEEE32.scaledMagnitude (normalized input i) *
      Wasm.IEEE32.scaledMagnitude (word weights (scaleOffset + i)) < 2 ^ scaleBound)
    (hAddUpper : addBound ≤ 276)
    (hAddRange : (Wasm.IEEE32.scaledValue (scaled weights input scaleOffset i) +
      Wasm.IEEE32.scaledValue (word weights (biasOffset + i))).natAbs < 2 ^ addBound) :
    CodeLib.IEEE32.Finite (word (layerNorm weights input scaleOffset biasOffset 1) i) ∧
      |CodeLib.IEEE32.value (word (layerNorm weights input scaleOffset biasOffset 1) i) -
        (C * I * CodeLib.IEEE32.value (word weights (scaleOffset + i)) + CodeLib.IEEE32.value (word weights (biasOffset + i)))| ≤
      componentError (CodeLib.IEEE32.value (centered input i)) I
        (CodeLib.IEEE32.value (word weights (scaleOffset + i))) centerError inverseError normBound scaleBound addBound := by
  rw [component_source weights input scaleOffset biasOffset i hi]
  have hNorm := F32ErrorPropagation.mul (centered input i) (inverse input) C I centerError inverseError normBound
    hCenter hInverse hNormLower hNormUpper hNormRange hCenterError hInverseError
  have hScaled := F32ErrorPropagation.mul (normalized input i) (word weights (scaleOffset + i))
    (C * I) (CodeLib.IEEE32.value (word weights (scaleOffset + i)))
    (F32MultiplicationBounds.epsilon normBound + (|CodeLib.IEEE32.value (centered input i)| * inverseError + centerError * |I|))
    0 scaleBound hNorm.1 hScale hScaleLower hScaleUpper hScaleRange hNorm.2 (by simp)
  simp only [mul_zero, zero_add] at hScaled
  have hAdd := F32ErrorPropagation.add (scaled weights input scaleOffset i) (word weights (biasOffset + i))
    (C * I * CodeLib.IEEE32.value (word weights (scaleOffset + i))) (CodeLib.IEEE32.value (word weights (biasOffset + i)))
    (F32MultiplicationBounds.epsilon scaleBound +
      (F32MultiplicationBounds.epsilon normBound + (|CodeLib.IEEE32.value (centered input i)| * inverseError + centerError * |I|)) *
        |CodeLib.IEEE32.value (word weights (scaleOffset + i))|) 0 addBound
    hScaled.1 hBias hAddUpper hAddRange hScaled.2 (by simp)
  simpa only [componentError, add_zero] using hAdd

#print axioms component_source
#print axioms component_error
end Project.Gpt2CachedStep.LayerNorm.Numerical
