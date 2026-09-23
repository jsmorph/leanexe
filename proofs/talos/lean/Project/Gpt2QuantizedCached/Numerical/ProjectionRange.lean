import Project.Gpt2QuantizedCached.Numerical.ProjectionOutputRange
import Project.Gpt2QuantizedCached.Numerical.ProjectionPair
import Project.Gpt2QuantizedCached.Numerical.VocabularyPair

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

def pairLayout (l : Layout) : ProjectionPair.Layout :=
  ⟨l.matrix.coefficientOffset, l.matrix.scaleOffset, l.quantizedBias, l.matrix.sourceOffset,
    l.referenceBias, l.matrix.inputWidth, l.matrix.outputWidth⟩

def pairBounds (p : Parameters) : ProjectionPair.Bounds :=
  ⟨quantizedBounds p, ⟨fun _ => p.referenceMul, fun _ => p.referenceAdd⟩, p.referenceBias⟩

theorem learned_weight (weights : ByteArray) (l : Layout)
    (hrow : l.matrix.rowStride = 1) (hcol : l.matrix.columnStride = l.matrix.outputWidth) (row : Nat) :
    weightWord weights l row = Gpt2LinearRows.Error.weightWord weights l.matrix.sourceOffset l.matrix.outputWidth row := by
  funext i
  simp only [weightWord, Gpt2LinearRows.Error.weightWord, hrow, hcol, Nat.mul_one]
  congr 1
  omega

theorem learned_ranges (reference quantized qi ri : ByteArray) (l : Layout)
    (w : WeightBounds) (v : VectorBounds) (scaleMagnitude : Nat) (p : Parameters)
    (hw : checkWeights reference quantized l w = true)
    (hv : checkVector ri l.matrix.inputWidth v = true)
    (ha : checkActivations qi scaleMagnitude = true)
    (hp : checkRanges l.matrix.inputWidth v.magnitude scaleMagnitude w p = true)
    (he : Export.check reference quantized = true) (hl : l.matrix ∈ Export.projections)
    (hs : qi.size = l.matrix.inputWidth * 4) (hb : l.withBias = true)
    (hrow : l.matrix.rowStride = 1) (hcol : l.matrix.columnStride = l.matrix.outputWidth)
    (row : Nat) (hr : row < l.matrix.outputWidth) :
    ProjectionPair.Ranges quantized qi reference ri (pairLayout l) row
      (activationError qi l.matrix.inputWidth) (fun _ => weightError quantized l row) (pairBounds p) := by
  have hq := output_ranges reference quantized qi l w v.magnitude scaleMagnitude p hw ha hp he hl hs row hr
  have hd := reference_ranges reference quantized ri l w v scaleMagnitude p hw hv hp row hr
  have hw := checked_weights reference quantized l w hw row hr
  have hv := checked_vector ri l.matrix.inputWidth v hv
  simp only [checkRanges, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hp
  have ht := reference_total (word ri) (weightWord reference l row) l.matrix.inputWidth v.magnitude w.magnitude p hp.1
    (fun i hi => (hv.2.2 i hi).1) (fun i hi => (hw.2.2.2.1 i hi).1)
    (fun i hi => (hv.2.2 i hi).2) (fun i hi => (hw.2.2.2.1 i hi).2.1)
  have hwEq := learned_weight reference l hrow hcol row
  have hBias := hw.2.2.2.2 hb
  refine ⟨?_, ?_, hBias.2.2.symm, hBias.1, hp.2.2.2.1, ?_⟩
  · rw [hb, hwEq] at hq
    exact hq
  · rw [hwEq] at hd
    exact hd
  · have h := bias_range _ _ _ _ _ ht.2 hBias.2.1 hp.2.2.2.2.2.1
    rw [hwEq] at h
    exact h

def vocabularyLayout : Layout :=
  ⟨⟨768, 50257, 0, 768, 1, Quantized.tokenWeightOffset, Quantized.tokenScaleOffset⟩, 0, 0, false⟩

theorem vocabulary_member : vocabularyLayout.matrix ∈ Export.projections := by
  exact List.mem_append_left _ (List.mem_singleton_self _)

noncomputable def vocabularyParameters (quantized qi : ByteArray) (p : Parameters) : VocabularyPair.Parameters :=
  ⟨fun _ => quantizedBounds p, fun _ => ⟨fun _ => p.referenceMul, fun _ => p.referenceAdd⟩,
    fun _ => activationError qi 768, fun row _ => weightError quantized vocabularyLayout row⟩

theorem vocabulary_ranges (reference quantized qi ri : ByteArray) (w : WeightBounds) (v : VectorBounds)
    (scaleMagnitude : Nat) (p : Parameters)
    (hw : checkWeights reference quantized vocabularyLayout w = true)
    (hv : checkVector ri 768 v = true) (ha : checkActivations qi scaleMagnitude = true)
    (hp : checkRanges 768 v.magnitude scaleMagnitude w p = true)
    (he : Export.check reference quantized = true) (hs : qi.size = 768 * 4) :
    VocabularyPair.Ranges quantized qi reference ri (vocabularyParameters quantized qi p) := by
  constructor
  · intro row hr
    have h := output_ranges reference quantized qi vocabularyLayout w v.magnitude scaleMagnitude p hw ha hp he vocabulary_member hs row hr
    have hwEq : weightWord reference vocabularyLayout row = fun i => word reference (row * 768 + i) := by
      funext i
      simp only [weightWord, vocabularyLayout, Nat.zero_add, Nat.mul_one]
    rw [hwEq] at h
    exact h
  · intro row hr
    have h := reference_ranges reference quantized ri vocabularyLayout w v scaleMagnitude p hw hv hp row hr
    have hwEq : weightWord reference vocabularyLayout row = fun i => word reference (row * 768 + i) := by
      funext i
      simp only [weightWord, vocabularyLayout, Nat.zero_add, Nat.mul_one]
    rw [hwEq] at h
    exact h

#print axioms learned_ranges
#print axioms vocabulary_ranges
end Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
