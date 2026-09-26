import Project.Gpt2QuantizedCached.Numerical.ProjectionRange
import Project.Gpt2QuantizedGroupedRows.UniformError

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionUniform
open LeanExe.Models.Gpt2 Project.ProofKit

noncomputable def referenceUpper (width mulBound addBound : Nat) : ℝ :=
  (width : ℝ) * (F32MultiplicationBounds.epsilon mulBound + F32AdditionBounds.epsilon addBound)

theorem reference_error (input : Nat → UInt32) (weights : Nat → ℝ) (width mulBound addBound : Nat) :
    F32DotError.errorBound input weights (fun _ => 0) (fun _ => 0) width
      ⟨fun _ => mulBound, fun _ => addBound⟩ = referenceUpper width mulBound addBound := by
  simp [F32DotError.errorBound, referenceUpper]
  ring

noncomputable def upper (width : Nat) (withBias : Bool)
    (inputMagnitude weightMagnitude inputError activationError weightError : ℝ)
    (p : ProjectionRangeCertificate.Parameters) : ℝ :=
  Gpt2QuantizedGroupedRows.UniformError.upper width withBias inputMagnitude weightMagnitude
    (activationError + inputError) weightError p.quantizedScale p.quantizedOutput p.quantizedAdd p.quantizedBias +
    ((if withBias then F32AdditionBounds.epsilon p.referenceBias else 0) +
      referenceUpper width p.referenceMul p.referenceAdd)

theorem learned_error_upper (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout) (row : Nat)
    (ex ew : Nat → ℝ) (E A D X W : ℝ) (p : ProjectionRangeCertificate.Parameters)
    (h : ProjectionPair.Ranges qw qi rw ri l row ex ew (ProjectionRangeCertificate.pairBounds p))
    (he : ∀ i < l.width, |CodeLib.IEEE32.value (word qi i) - CodeLib.IEEE32.value (word ri i)| ≤ E)
    (hE : 0 ≤ E) (hA : ∀ i < l.width, 0 ≤ ex i ∧ ex i ≤ A)
    (hD : ∀ i < l.width, 0 ≤ ew i ∧ ew i ≤ D)
    (hX : ∀ i < l.width, |ProjectionPair.inputValues ri i| ≤ X)
    (hW : ∀ i < l.width, |ProjectionPair.weightValues rw l row i| ≤ W) :
    ProjectionPair.error qw qi rw ri l row (fun _ => E) ex ew (ProjectionRangeCertificate.pairBounds p) ≤
      upper l.width true X W E A D p := by
  have ht := ProjectionPair.transfer_input qw qi l row true (ProjectionPair.inputValues qi)
    (ProjectionPair.inputValues ri) (ProjectionPair.weightValues rw l row) ex (fun _ => E) ew
    (ProjectionRangeCertificate.quantizedBounds p) h.quantized he
  have hq := Gpt2QuantizedGroupedRows.UniformError.error_upper qw qi l.qWeight l.qScale l.qBias l.width row true
    (ProjectionPair.inputValues ri) (ProjectionPair.weightValues rw l row) (fun i => ex i + E) ew X W (A + E) D
    p.quantizedScale p.quantizedOutput p.quantizedAdd p.quantizedBias ht hX hW
    (fun i hi => ⟨add_nonneg (hA i hi).1 hE, add_le_add (hA i hi).2 le_rfl⟩) hD
  unfold ProjectionPair.error
  dsimp only [ProjectionRangeCertificate.pairBounds]
  rw [reference_error]
  exact add_le_add hq le_rfl

theorem vocabulary_error_upper (qw qi rw ri : ByteArray) (row : Nat) (E A D X W : ℝ)
    (p : ProjectionRangeCertificate.Parameters)
    (h : VocabularyPair.Ranges qw qi rw ri (ProjectionRangeCertificate.vocabularyParameters qw qi p))
    (hr : row < 50257) (he : Close qi ri 768 E) (hE : 0 ≤ E)
    (hA : ∀ i < 768, 0 ≤ ProjectionRangeCertificate.activationError qi 768 i ∧
      ProjectionRangeCertificate.activationError qi 768 i ≤ A)
    (hD : 0 ≤ ProjectionRangeCertificate.weightError qw ProjectionRangeCertificate.vocabularyLayout row ∧
      ProjectionRangeCertificate.weightError qw ProjectionRangeCertificate.vocabularyLayout row ≤ D)
    (hX : ∀ i < 768, |ProjectionPair.inputValues ri i| ≤ X)
    (hW : ∀ i < 768, |VocabularyPair.weights rw row i| ≤ W) :
    VocabularyPair.componentError qw qi rw ri E (ProjectionRangeCertificate.vocabularyParameters qw qi p) row ≤
      upper 768 false X W E A D p := by
  have ht := ProjectionPair.transfer_input qw qi VocabularyPair.layout row false (ProjectionPair.inputValues qi)
    (ProjectionPair.inputValues ri) (VocabularyPair.weights rw row)
    (ProjectionRangeCertificate.activationError qi 768) (fun _ => E)
    (fun _ => ProjectionRangeCertificate.weightError qw ProjectionRangeCertificate.vocabularyLayout row)
    (ProjectionRangeCertificate.quantizedBounds p) (h.quantized row hr) he
  have hq := Gpt2QuantizedGroupedRows.UniformError.error_upper qw qi VocabularyPair.layout.qWeight VocabularyPair.layout.qScale 0 768 row false
    (ProjectionPair.inputValues ri) (VocabularyPair.weights rw row)
    (fun i => ProjectionRangeCertificate.activationError qi 768 i + E)
    (fun _ => ProjectionRangeCertificate.weightError qw ProjectionRangeCertificate.vocabularyLayout row)
    X W (A + E) D p.quantizedScale p.quantizedOutput p.quantizedAdd p.quantizedBias ht hX hW
    (fun i hi => ⟨add_nonneg (hA i hi).1 hE, add_le_add (hA i hi).2 le_rfl⟩) (fun _ _ => hD)
  unfold VocabularyPair.componentError
  dsimp only [ProjectionRangeCertificate.vocabularyParameters]
  rw [reference_error]
  simp only [upper, Bool.false_eq_true, ite_false, zero_add]
  exact add_le_add hq le_rfl

#print axioms learned_error_upper
#print axioms vocabulary_error_upper
end Project.Gpt2QuantizedCached.Numerical.ProjectionUniform
