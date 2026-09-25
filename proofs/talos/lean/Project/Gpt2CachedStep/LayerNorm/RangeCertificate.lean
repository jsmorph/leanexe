import Project.Gpt2CachedStep.LayerNorm.RangeCheck
import Project.Gpt2CachedStep.LayerNorm.ForwardError
import Project.ProofKit.F32RangeCertificate
import Project.ProofKit.F32UniformRange
import Project.ProofKit.F32SumRangeCertificate

namespace Project.Gpt2CachedStep.LayerNorm.RangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

def bounds (p : Parameters) : ForwardError.Bounds :=
  ⟨fun _ => p.meanAdd, p.meanDiv, fun _ => p.centerSub, fun _ => p.varianceMul,
    fun _ => p.varianceAdd, p.varianceDiv, p.epsilonAdd, p.squareRoot, p.reciprocal,
    fun _ => p.normalizedMul, fun _ => p.scaleMul, fun _ => p.biasAdd⟩

theorem meanPrefix_source (input : ByteArray) (count : Nat) :
    F32SumError.sumPrefix (fun i => word input i) count = Project.Gpt2RowMean.sumPrefix input 0 count := by
  simp only [F32SumError.sumPrefix, Project.Gpt2RowMean.sumPrefix, Nat.zero_mul, Nat.zero_add]

theorem meanSum_source (input : ByteArray) : meanSum input = Project.Gpt2RowMean.sumPrefix input 0 768 := by
  simp only [meanSum, Project.Gpt2RowMean.sumPrefix, Nat.zero_mul, Nat.zero_add]

theorem variancePrefix_source (input : ByteArray) (mean : UInt32) (count : Nat) :
    F32DotError.compute (centered input mean) (centered input mean) count =
      Project.Gpt2RowInvStd.variancePrefix input 0 mean count := by
  simp only [F32DotError.compute, F32SumError.sumPrefix, centered, Project.Gpt2RowInvStd.variancePrefix,
    Nat.zero_mul, Nat.zero_add]

theorem varianceSum_source (input : ByteArray) (mean : UInt32) :
    varianceSum input mean = Project.Gpt2RowInvStd.variancePrefix input 0 mean 768 := by
  simp only [varianceSum, centered, Project.Gpt2RowInvStd.variancePrefix, Nat.zero_mul, Nat.zero_add]

theorem mean_source (input : ByteArray) :
    LeanExe.Float32.divBits (meanSum input) 0x44400000 = rowMean input 0 := by
  rw [meanSum_source, Project.Gpt2RowMean.rowMean_eq, F32Div.div_eq]

theorem inverse_source (input : ByteArray) (mean : UInt32) :
    LeanExe.Float32.divBits 0x3F800000 (LeanExe.Float32.sqrtBits (LeanExe.Float32.addBits
      (LeanExe.Float32.divBits (varianceSum input mean) 0x44400000) 0x3727C5AC)) = rowInvStd input 0 mean := by
  rw [varianceSum_source, Project.Gpt2RowInvStd.rowInvStd_eq, F32Div.div_eq, F32Sqrt.sqrt_eq,
    F32Add.add_eq, F32Div.div_eq]

theorem sound (weights input : ByteArray) (scaleOffset biasOffset : Nat) (p : Parameters)
    (h : check weights input scaleOffset biasOffset p = true) :
    ForwardError.Ranges weights input scaleOffset biasOffset (bounds p) := by
  simp only [check, mean_source, inverse_source, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨hMeanUpper, hMeanFits, hVarUpper, hVarFits, hMean, hVar, hEps, hRoot, hInv, hComponents⟩ := h
  have hSub (i : Nat) (hi : i < 768) := (hComponents i hi).2.2.2.2.1
  have hSquare (i : Nat) (hi : i < 768) := (hComponents i hi).2.2.2.2.2.1
  have hNorm (i : Nat) (hi : i < 768) := (hComponents i hi).2.2.2.2.2.2.1
  have hScale (i : Nat) (hi : i < 768) := (hComponents i hi).2.2.2.2.2.2.2.1
  have hBias (i : Nat) (hi : i < 768) := (hComponents i hi).2.2.2.2.2.2.2.2
  simp only [F32RangeCertificate.division, F32RangeCertificate.addition, F32RangeCertificate.squareRoot,
    F32RangeCertificate.subtraction, F32RangeCertificate.multiplication,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, and_assoc] at hMean hVar hEps hRoot hInv hSub hSquare hNorm hScale hBias
  have hInput (i : Nat) (hi : i < 768) : CodeLib.IEEE32.Finite (word input i) := (hComponents i hi).1
  have hm := F32SumRangeCertificate.ranges (fun i => word input i) p.meanAdd 768 hMeanFits
  have hMulLower : 173 ≤ p.varianceMul := (hSquare 0 (by decide)).2.2.1
  have hMulUpper : p.varianceMul ≤ 425 := (hSquare 0 (by decide)).2.2.2.1
  have hProduct (i : Nat) (hi : i < 768) :
      Wasm.IEEE32.scaledMagnitude (centered input (rowMean input 0) i) *
        Wasm.IEEE32.scaledMagnitude (centered input (rowMean input 0) i) < 2 ^ p.varianceMul := (hSquare i hi).2.2.2.2
  have hv := F32SumRangeCertificate.ranges (fun i => LeanExe.Float32.mulBits
    (centered input (rowMean input 0) i) (centered input (rowMean input 0) i)) p.varianceAdd 768 hVarFits
  have hDen : Project.Gpt2RowInvStd.DenominatorError.Ranges (varianceSum input (rowMean input 0))
      p.varianceDiv p.epsilonAdd p.squareRoot p.reciprocal := by
    have hs : Wasm.IEEE32.sign (LeanExe.Float32.addBits
        (LeanExe.Float32.divBits (varianceSum input (rowMean input 0)) 0x44400000) 0x3727C5AC) = false := by
      have hn := hRoot.2.1
      cases he : Wasm.IEEE32.sign (LeanExe.Float32.addBits
        (LeanExe.Float32.divBits (varianceSum input (rowMean input 0)) 0x44400000) 0x3727C5AC) <;> simp_all
    exact ⟨hVar.2.2.1, hVar.2.2.2.1, hVar.2.2.2.2.2, hEps.2.2.1, hEps.2.2.2,
      hRoot.2.2.1, hRoot.2.2.2.1, hRoot.2.2.2.2, hs, hInv.2.2.1, hInv.2.2.2.1, hInv.2.2.2.2.1, hInv.2.2.2.2.2⟩
  refine {
    inputFinite := hInput
    scaleFinite := fun i hi => (hComponents i hi).2.1
    biasFinite := fun i hi => (hComponents i hi).2.2.1
    meanAddUpper := fun _ _ => hMeanUpper
    meanAddRange := ?_
    meanDivLower := hMean.2.2.1
    meanDivUpper := hMean.2.2.2.1
    meanDivRange := ?_
    centerUpper := fun i hi => (hSub i hi).2.2.1
    centerRange := fun i hi => (hSub i hi).2.2.2
    varianceMulLower := fun _ _ => hMulLower
    varianceMulUpper := fun _ _ => hMulUpper
    varianceMulRange := hProduct
    varianceAddUpper := fun _ _ => hVarUpper
    varianceAddRange := ?_
    denominator := ?_
    normalizedLower := fun i hi => (hNorm i hi).2.2.1
    normalizedUpper := fun i hi => (hNorm i hi).2.2.2.1
    normalizedRange := fun i hi => (hNorm i hi).2.2.2.2
    scaleLower := fun i hi => (hScale i hi).2.2.1
    scaleUpper := fun i hi => (hScale i hi).2.2.2.1
    scaleRange := fun i hi => (hScale i hi).2.2.2.2
    biasUpper := fun i hi => (hBias i hi).2.2.1
    biasRange := fun i hi => (hBias i hi).2.2.2 }
  · simpa only [bounds, meanPrefix_source] using hm
  · simpa only [bounds, meanSum_source] using hMean.2.2.2.2.2
  · change ∀ i < 768, (Wasm.IEEE32.scaledValue
      (F32DotError.compute (centered input (rowMean input 0)) (centered input (rowMean input 0)) i) +
      Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (centered input (rowMean input 0) i)
        (centered input (rowMean input 0) i))).natAbs < 2 ^ p.varianceAdd at hv
    simpa only [bounds, variancePrefix_source, centered, Numerical.centered] using hv
  · simpa only [bounds, varianceSum_source] using hDen

#print axioms sound
end Project.Gpt2CachedStep.LayerNorm.RangeCertificate
