import Project.Gpt2CachedStep.LayerNorm.Numerical

namespace Project.Gpt2CachedStep.LayerNorm.ForwardError
open LeanExe.Models.Gpt2 Project.ProofKit

structure Bounds where
  meanAdd : Nat → Nat
  meanDiv : Nat
  centerSub : Nat → Nat
  varianceMul : Nat → Nat
  varianceAdd : Nat → Nat
  varianceDiv : Nat
  epsilonAdd : Nat
  squareRoot : Nat
  reciprocal : Nat
  normalizedMul : Nat → Nat
  scaleMul : Nat → Nat
  biasAdd : Nat → Nat

noncomputable def referenceMean (X : Nat → ℝ) : ℝ := (∑ i ∈ Finset.range 768, X i) / 768
noncomputable def referenceSquares (X : Nat → ℝ) : ℝ := ∑ i ∈ Finset.range 768, (X i - referenceMean X) ^ 2
noncomputable def referenceInverse (X : Nat → ℝ) : ℝ := 1 / Project.Gpt2RowInvStd.DenominatorError.referenceRoot (referenceSquares X)

noncomputable def meanError (ex : Nat → ℝ) (bounds : Bounds) : ℝ :=
  F32AverageError.error ex bounds.meanAdd bounds.meanDiv

noncomputable def centerError (ex : Nat → ℝ) (bounds : Bounds) (i : Nat) : ℝ :=
  Project.Gpt2RowInvStd.Error.deltaError ex (meanError ex bounds) bounds.centerSub i

noncomputable def squaresError (input : ByteArray) (X ex : Nat → ℝ) (bounds : Bounds) : ℝ :=
  Project.Gpt2RowInvStd.Error.varianceError input 0 (rowMean input 0) X (referenceMean X)
    (centerError ex bounds) bounds.varianceMul bounds.varianceAdd

noncomputable def inverseError (input : ByteArray) (X ex : Nat → ℝ) (bounds : Bounds)
    (rootLower denominatorLower : ℝ) : ℝ :=
  Project.Gpt2RowInvStd.DenominatorError.inverseError (referenceSquares X) (squaresError input X ex bounds)
    rootLower denominatorLower bounds.varianceDiv bounds.epsilonAdd bounds.squareRoot bounds.reciprocal

structure Ranges (weights input : ByteArray) (scaleOffset biasOffset : Nat) (bounds : Bounds) : Prop where
  inputFinite : ∀ i < 768, CodeLib.IEEE32.Finite (word input i)
  scaleFinite : ∀ i < 768, CodeLib.IEEE32.Finite (word weights (scaleOffset + i))
  biasFinite : ∀ i < 768, CodeLib.IEEE32.Finite (word weights (biasOffset + i))
  meanAddUpper : ∀ i < 768, bounds.meanAdd i ≤ 276
  meanAddRange : ∀ i < 768,
    (Wasm.IEEE32.scaledValue (Project.Gpt2RowMean.sumPrefix input 0 i) + Wasm.IEEE32.scaledValue (word input i)).natAbs < 2 ^ bounds.meanAdd i
  meanDivLower : 24 ≤ bounds.meanDiv
  meanDivUpper : bounds.meanDiv ≤ 275
  meanDivRange : Wasm.IEEE32.scaledMagnitude (Project.Gpt2RowMean.sumPrefix input 0 768) * 2 ^ 149 ≤
    Wasm.IEEE32.scaledMagnitude 0x44400000 * 2 ^ bounds.meanDiv
  centerUpper : ∀ i < 768, bounds.centerSub i ≤ 276
  centerRange : ∀ i < 768,
    (Wasm.IEEE32.scaledValue (word input i) - Wasm.IEEE32.scaledValue (rowMean input 0)).natAbs < 2 ^ bounds.centerSub i
  varianceMulLower : ∀ i < 768, 173 ≤ bounds.varianceMul i
  varianceMulUpper : ∀ i < 768, bounds.varianceMul i ≤ 425
  varianceMulRange : ∀ i < 768,
    Wasm.IEEE32.scaledMagnitude (Numerical.centered input i) * Wasm.IEEE32.scaledMagnitude (Numerical.centered input i) < 2 ^ bounds.varianceMul i
  varianceAddUpper : ∀ i < 768, bounds.varianceAdd i ≤ 276
  varianceAddRange : ∀ i < 768,
    (Wasm.IEEE32.scaledValue (Project.Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) i) +
      Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (Numerical.centered input i) (Numerical.centered input i))).natAbs < 2 ^ bounds.varianceAdd i
  denominator : Project.Gpt2RowInvStd.DenominatorError.Ranges (Project.Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) 768)
    bounds.varianceDiv bounds.epsilonAdd bounds.squareRoot bounds.reciprocal
  normalizedLower : ∀ i < 768, 173 ≤ bounds.normalizedMul i
  normalizedUpper : ∀ i < 768, bounds.normalizedMul i ≤ 425
  normalizedRange : ∀ i < 768,
    Wasm.IEEE32.scaledMagnitude (Numerical.centered input i) * Wasm.IEEE32.scaledMagnitude (Numerical.inverse input) < 2 ^ bounds.normalizedMul i
  scaleLower : ∀ i < 768, 173 ≤ bounds.scaleMul i
  scaleUpper : ∀ i < 768, bounds.scaleMul i ≤ 425
  scaleRange : ∀ i < 768,
    Wasm.IEEE32.scaledMagnitude (Numerical.normalized input i) * Wasm.IEEE32.scaledMagnitude (word weights (scaleOffset + i)) < 2 ^ bounds.scaleMul i
  biasUpper : ∀ i < 768, bounds.biasAdd i ≤ 276
  biasRange : ∀ i < 768,
    (Wasm.IEEE32.scaledValue (Numerical.scaled weights input scaleOffset i) +
      Wasm.IEEE32.scaledValue (word weights (biasOffset + i))).natAbs < 2 ^ bounds.biasAdd i

noncomputable def componentError (weights input : ByteArray) (scaleOffset : Nat) (X ex : Nat → ℝ)
    (bounds : Bounds) (rootLower denominatorLower : ℝ) (i : Nat) : ℝ :=
  Numerical.componentError (CodeLib.IEEE32.value (Numerical.centered input i)) (referenceInverse X)
    (CodeLib.IEEE32.value (word weights (scaleOffset + i))) (centerError ex bounds i)
    (inverseError input X ex bounds rootLower denominatorLower)
    (bounds.normalizedMul i) (bounds.scaleMul i) (bounds.biasAdd i)

theorem component_error (weights input : ByteArray) (scaleOffset biasOffset : Nat)
    (X ex : Nat → ℝ) (bounds : Bounds) (rootLower denominatorLower : ℝ)
    (hRanges : Ranges weights input scaleOffset biasOffset bounds)
    (hInputError : ∀ i < 768, |CodeLib.IEEE32.value (word input i) - X i| ≤ ex i)
    (hRootPositive : 0 < rootLower)
    (hRootLower : rootLower ≤ Real.sqrt (CodeLib.IEEE32.value
      (Project.Gpt2RowInvStd.DenominatorError.shifted (Project.Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) 768))) +
        Project.Gpt2RowInvStd.DenominatorError.referenceRoot (referenceSquares X))
    (hDenPositive : 0 < denominatorLower)
    (hDenLower : denominatorLower ≤ |CodeLib.IEEE32.value (Project.Gpt2RowInvStd.DenominatorError.denominator (Project.Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) 768))|)
    (i : Nat) (hi : i < 768) :
    CodeLib.IEEE32.Finite (word (layerNorm weights input scaleOffset biasOffset 1) i) ∧
      |CodeLib.IEEE32.value (word (layerNorm weights input scaleOffset biasOffset 1) i) -
        ((X i - referenceMean X) * referenceInverse X * CodeLib.IEEE32.value (word weights (scaleOffset + i)) +
          CodeLib.IEEE32.value (word weights (biasOffset + i)))| ≤
        componentError weights input scaleOffset X ex bounds rootLower denominatorLower i := by
  have hMean := Project.Gpt2RowInvStd.Error.mean_error input 0 X ex bounds.meanAdd bounds.meanDiv
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hRanges.inputFinite)
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hInputError) hRanges.meanAddUpper
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hRanges.meanAddRange)
    hRanges.meanDivLower hRanges.meanDivUpper hRanges.meanDivRange
  have hCenter (j : Nat) (hj : j < 768) := Project.Gpt2RowInvStd.Error.centered_error input 0 (rowMean input 0)
    X ex (referenceMean X) (meanError ex bounds) bounds.centerSub
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hRanges.inputFinite) hMean.1
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hInputError) hMean.2
    hRanges.centerUpper (by simpa only [Nat.zero_mul, Nat.zero_add] using hRanges.centerRange) j hj
  have hVariance := Project.Gpt2RowInvStd.Error.variance_error input 0 (rowMean input 0) X (referenceMean X)
    (centerError ex bounds) bounds.varianceMul bounds.varianceAdd
    (fun j hj => (hCenter j hj).1) (fun j hj => (hCenter j hj).2)
    hRanges.varianceMulLower hRanges.varianceMulUpper
    (by simpa only [Project.Gpt2RowInvStd.Error.delta, Numerical.centered, Nat.zero_mul, Nat.zero_add] using hRanges.varianceMulRange)
    hRanges.varianceAddUpper
    (by simpa only [Project.Gpt2RowInvStd.Error.delta, Numerical.centered, Nat.zero_mul, Nat.zero_add] using hRanges.varianceAddRange)
  have hSquares : 0 ≤ referenceSquares X := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hInverse := Project.Gpt2RowInvStd.DenominatorError.inverse_error (Project.Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) 768)
    (referenceSquares X) (squaresError input X ex bounds) rootLower denominatorLower
    bounds.varianceDiv bounds.epsilonAdd bounds.squareRoot bounds.reciprocal
    hVariance.1 hSquares hVariance.2 hRanges.denominator hRootPositive hRootLower hDenPositive hDenLower
  rw [← Project.Gpt2RowInvStd.DenominatorError.source_inverse] at hInverse
  exact Numerical.component_error weights input scaleOffset biasOffset i hi (X i - referenceMean X)
    (referenceInverse X) (centerError ex bounds i) (inverseError input X ex bounds rootLower denominatorLower)
    (bounds.normalizedMul i) (bounds.scaleMul i) (bounds.biasAdd i)
    (by simpa only [Project.Gpt2RowInvStd.Error.delta, Numerical.centered, Nat.zero_mul, Nat.zero_add] using (hCenter i hi).1)
    hInverse.1 (hRanges.scaleFinite i hi) (hRanges.biasFinite i hi)
    (by simpa only [centerError, Project.Gpt2RowInvStd.Error.delta, Numerical.centered, Nat.zero_mul, Nat.zero_add] using (hCenter i hi).2)
    hInverse.2 (hRanges.normalizedLower i hi) (hRanges.normalizedUpper i hi) (hRanges.normalizedRange i hi)
    (hRanges.scaleLower i hi) (hRanges.scaleUpper i hi) (hRanges.scaleRange i hi) (hRanges.biasUpper i hi) (hRanges.biasRange i hi)

#print axioms component_error
end Project.Gpt2CachedStep.LayerNorm.ForwardError
