import Project.Gpt2QuantizedCached.Numerical.ProjectionActivation
import Project.Gpt2QuantizedCached.Export
import Project.Gpt2QuantizedGroupedRows.OutputError

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit Gpt2QuantizedGroupedRows
open Gpt2QuantizedGroupedRows.ForwardError

def quantizedBounds (p : Parameters) : OutputError.Bounds :=
  ⟨fun _ => p.quantizedScale, fun _ => p.quantizedOutput, fun _ => p.quantizedAdd, p.quantizedBias⟩

noncomputable def activationError (input : ByteArray) (width i : Nat) : ℝ :=
  CodeLib.IEEE32.value (inputScale input width 1 0 (i / 64)) * (1 / 2 + 1 / 65536)

noncomputable def weightError (weights : ByteArray) (l : Layout) (row : Nat) : ℝ :=
  CodeLib.IEEE32.value (weightScale weights l row) * (3 / 2 + 1 / 65536)

theorem exported_weight (reference quantized : ByteArray) (l : Layout) (row i : Nat)
    (h : Export.check reference quantized = true) (hl : l.matrix ∈ Export.projections)
    (hr : row < l.matrix.outputWidth) (hi : i < l.matrix.inputWidth) :
    |CodeLib.IEEE32.value (weightScale quantized l row) * QuantizedGroupError.byteValue quantized
        (l.matrix.coefficientOffset + row * l.matrix.inputWidth + i) -
      CodeLib.IEEE32.value (weightWord reference l row i)| ≤ weightError quantized l row := by
  have hc := Export.projection_checked reference quantized h l.matrix hl row hr
  have he := QuantizedRangeCertificate.reconstruction_uniform _ _ _ _ _ hc i hi
  rw [Export.sourceRow_word _ _ _ _ hi] at he
  exact he

theorem group_ranges (reference quantized input : ByteArray) (l : Layout)
    (w : WeightBounds) (inputMagnitude scaleMagnitude : Nat) (p : Parameters)
    (hw : checkWeights reference quantized l w = true)
    (ha : checkActivations input scaleMagnitude = true)
    (hp : checkRanges l.matrix.inputWidth inputMagnitude scaleMagnitude w p = true)
    (he : Export.check reference quantized = true) (hl : l.matrix ∈ Export.projections)
    (hs : input.size = l.matrix.inputWidth * 4)
    (row group : Nat) (hr : row < l.matrix.outputWidth) (hg : group < l.matrix.inputWidth / 64) :
    GroupRanges quantized input l.matrix.coefficientOffset l.matrix.scaleOffset l.matrix.inputWidth 1 0 row group
      p.quantizedScale p.quantizedOutput (fun i => CodeLib.IEEE32.value (word input i))
      (fun i => CodeLib.IEEE32.value (weightWord reference l row i))
      (activationError input l.matrix.inputWidth) (fun _ => weightError quantized l row) := by
  have hi := activation_conditions input l.matrix.inputWidth scaleMagnitude group hs hg ha
  have hw := checked_weights reference quantized l w hw row hr
  have hInput : ∀ i < 64, (Quantized.quantizeRows input 64 (1 * (l.matrix.inputWidth / 64))).values[
      0 * l.matrix.inputWidth + group * 64 + i]! ≠ 128 := by
    intro i hit
    apply QuantizedValue.quantizeRows_valid
    simp only [Nat.one_mul, Nat.zero_mul, Nat.zero_add]
    omega
  have hWeight : ∀ i < 64, quantized[l.matrix.coefficientOffset + row * l.matrix.inputWidth + group * 64 + i]! ≠ 128 := by
    intro i hit
    simpa only [Nat.add_assoc] using (hw.2.2.2.1 (group * 64 + i) (by omega)).2.2
  have hacc := group_accumulator_bound quantized (Quantized.quantizeRows input 64 (1 * (l.matrix.inputWidth / 64))).values
    (l.matrix.coefficientOffset + row * l.matrix.inputWidth + group * 64)
    (0 * l.matrix.inputWidth + group * 64) 64 (by decide) hInput hWeight
  have habs : (LeanExe.Signed32.decode
      (accumulator quantized input l.matrix.coefficientOffset l.matrix.inputWidth 1 0 row group)).natAbs ≤ 1032256 := by
    rw [← Int.natCast_natAbs] at hacc
    exact_mod_cast hacc
  simp only [checkRanges, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hp
  have hscale := QuantizedUniformRange.rescale_ranges
    (accumulator quantized input l.matrix.coefficientOffset l.matrix.inputWidth 1 0 row group)
    (inputScale input l.matrix.inputWidth 1 0 group) (weightScale quantized l row)
    scaleMagnitude w.scaleMagnitude p.quantizedScale p.quantizedOutput hp.2.1 habs hi.1 hw.1 hi.2.1 hw.2.1
  have hb := hp.2.1
  simp only [F32UniformRange.rescaleFits, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hb
  refine ⟨hInput, hWeight, ?_, ?_, hi.1, hw.1, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hscale.1, hscale.2.1⟩
  · intro i hit
    have heq : (group * 64 + i) / 64 = group := by omega
    simpa only [activationError, heq, Nat.one_mul, Nat.zero_mul, Nat.zero_add] using hi.2.2 i hit
  · intro i hit
    simpa only [Nat.add_assoc, weightScale, ForwardError.weightScale] using
      exported_weight reference quantized l row (group * 64 + i) he hl hr (by omega)

#print axioms exported_weight
#print axioms group_ranges
end Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
