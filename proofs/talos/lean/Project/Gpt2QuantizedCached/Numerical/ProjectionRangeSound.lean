import Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCheck
import Project.ProofKit.QuantizedUniformRange

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

theorem checked_vector (input : ByteArray) (width : Nat) (b : VectorBounds)
    (h : checkVector input width b = true) :
    input.size = width * 4 ∧ magnitudeSum (word input) width ≤ b.sum ∧
      ∀ i < width, CodeLib.IEEE32.Finite (word input i) ∧
        Wasm.IEEE32.scaledMagnitude (word input i) ≤ b.magnitude := by
  simpa only [checkVector, CodeLib.IEEE32.Finite, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] using h

theorem checked_weights (reference quantized : ByteArray) (l : Layout) (b : WeightBounds)
    (h : checkWeights reference quantized l b = true) (row : Nat) (hr : row < l.matrix.outputWidth) :
    CodeLib.IEEE32.Finite (weightScale quantized l row) ∧
      Wasm.IEEE32.scaledMagnitude (weightScale quantized l row) ≤ b.scaleMagnitude ∧
      magnitudeSum (weightWord reference l row) l.matrix.inputWidth ≤ b.rowSum ∧
      (∀ i < l.matrix.inputWidth, CodeLib.IEEE32.Finite (weightWord reference l row i) ∧
        Wasm.IEEE32.scaledMagnitude (weightWord reference l row i) ≤ b.magnitude ∧
        quantized[l.matrix.coefficientOffset + row * l.matrix.inputWidth + i]! ≠ 128) ∧
      (l.withBias = true → CodeLib.IEEE32.Finite (word reference (l.referenceBias + row)) ∧
        Wasm.IEEE32.scaledMagnitude (word reference (l.referenceBias + row)) ≤ b.biasMagnitude ∧
        word reference (l.referenceBias + row) =
          LeanExe.Packed.getUInt32LE! quantized (l.quantizedBias + row * 4)) := by
  simp only [checkWeights, List.all_eq_true, List.mem_range] at h
  have h := h row hr
  cases hb : l.withBias <;>
    simpa only [hb, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
      false_implies, true_implies, and_true, CodeLib.IEEE32.Finite, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq, bne_iff_ne, List.all_eq_true, List.mem_range, and_assoc] using h

theorem reference_ranges (reference quantized input : ByteArray) (l : Layout)
    (w : WeightBounds) (v : VectorBounds) (a : Nat) (p : Parameters)
    (hw : checkWeights reference quantized l w = true)
    (hv : checkVector input l.matrix.inputWidth v = true)
    (hp : checkRanges l.matrix.inputWidth v.magnitude a w p = true)
    (row : Nat) (hr : row < l.matrix.outputWidth) :
    F32DotError.Ranges (word input) (weightWord reference l row) l.matrix.inputWidth
      ⟨fun _ => p.referenceMul, fun _ => p.referenceAdd⟩ := by
  have hw := checked_weights reference quantized l w hw row hr
  have hv := checked_vector input l.matrix.inputWidth v hv
  simp only [checkRanges, Bool.and_eq_true, and_assoc] at hp
  exact F32UniformRange.dotFits_sound _ _ _ _ _ _ _ hp.1
    (fun i hi => (hv.2.2 i hi).1) (fun i hi => (hw.2.2.2.1 i hi).1)
    (fun i hi => (hv.2.2 i hi).2) (fun i hi => (hw.2.2.2.1 i hi).2.1)

theorem reference_total (x w : Nat → UInt32) (width inputMagnitude weightMagnitude : Nat)
    (p : Parameters) (h : F32UniformRange.dotFits width inputMagnitude weightMagnitude
      p.referenceMul p.referenceAdd = true)
    (hx : ∀ i < width, CodeLib.IEEE32.Finite (x i))
    (hw : ∀ i < width, CodeLib.IEEE32.Finite (w i))
    (hX : ∀ i < width, Wasm.IEEE32.scaledMagnitude (x i) ≤ inputMagnitude)
    (hW : ∀ i < width, Wasm.IEEE32.scaledMagnitude (w i) ≤ weightMagnitude) :
    CodeLib.IEEE32.Finite (F32DotError.compute x w width) ∧
      (Wasm.IEEE32.scaledValue (F32DotError.compute x w width)).natAbs ≤
        sumMagnitude width p.referenceMul p.referenceAdd := by
  have hr := F32UniformRange.dotFits_sound x w width inputMagnitude weightMagnitude
    p.referenceMul p.referenceAdd h hx hw hX hW
  have hm (i : Nat) (hi : i < width) := F32UniformRange.product_magnitude (x i) (w i)
    p.referenceMul (hr.mulLower i hi) (hr.mulUpper i hi) (hx i hi) (hw i hi) (hr.mulRange i hi)
  simp only [F32UniformRange.dotFits, Bool.and_eq_true, and_assoc] at h
  exact (F32UniformRange.sumFits_sound _ _ _ _ h.2.2.2
    (fun i hi => (hm i hi).1) (fun i hi => (hm i hi).2)).2

theorem bias_range (total bias : UInt32) (totalMagnitude biasMagnitude bound : Nat)
    (ht : (Wasm.IEEE32.scaledValue total).natAbs ≤ totalMagnitude)
    (hb : Wasm.IEEE32.scaledMagnitude bias ≤ biasMagnitude)
    (h : totalMagnitude + biasMagnitude < 2 ^ bound) :
    (Wasm.IEEE32.scaledValue total + Wasm.IEEE32.scaledValue bias).natAbs < 2 ^ bound := by
  have hb' : (Wasm.IEEE32.scaledValue bias).natAbs ≤ biasMagnitude := by
    simpa only [CodeLib.IEEE32.natAbs_scaledValue] using hb
  exact (Int.natAbs_add_le _ _).trans_lt ((Nat.add_le_add ht hb').trans_lt h)

#print axioms checked_weights
#print axioms reference_ranges
#print axioms reference_total
#print axioms bias_range
end Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
