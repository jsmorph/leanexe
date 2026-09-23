import Project.Gpt2QuantizedCached.Numerical.OperationUpperSound

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionUpper
open LeanExe.Models.Gpt2 Project.ProofKit OperationUpper

structure Conditions (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout) (d : ProjectionData)
    (ex ew : Nat → Nat → ℝ) : Prop where
  ranges : ∀ j < l.outputWidth, ProjectionPair.Ranges qw qi rw ri l j (ex j) (ew j) (ProjectionRangeCertificate.pairBounds d.bounds)
  activation : ∀ j < l.outputWidth, ∀ i < l.width, 0 ≤ ex j i ∧ ex j i ≤ DyadicUpper.value d.activationError
  weight : ∀ j < l.outputWidth, ∀ i < l.width, 0 ≤ ew j i ∧ ew j i ≤ DyadicUpper.value d.weightError
  inputMagnitude : ∀ i < l.width, |ProjectionPair.inputValues ri i| ≤ DyadicUpper.value d.inputMagnitude
  weightMagnitude : ∀ j < l.outputWidth, ∀ i < l.width, |ProjectionPair.weightValues rw l j i| ≤ DyadicUpper.value d.weightMagnitude

theorem learned_close (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout) (d : ProjectionData)
    (ex ew : Nat → Nat → ℝ) (h : Conditions qw qi rw ri l d ex ew) (hw : 64 ∣ l.width)
    (E : Nat) (he : Close qi ri l.width (DyadicUpper.value E)) :
    Close (Quantized.linearGroupedRows qw qi l.qWeight l.qScale l.qBias l.width l.outputWidth 1 true)
      (linearRows rw ri l.rWeight l.rBias l.width l.outputWidth 1) l.outputWidth
      (DyadicUpper.value (project l.width true d E)) := by
  intro j hj
  have hp := ProjectionPair.component_error qw qi rw ri l j hj hw (fun _ => DyadicUpper.value E)
    (ex j) (ew j) (ProjectionRangeCertificate.pairBounds d.bounds) (h.ranges j hj) he
  have hu := ProjectionUniform.learned_error_upper qw qi rw ri l j (ex j) (ew j)
    (DyadicUpper.value E) (DyadicUpper.value d.activationError) (DyadicUpper.value d.weightError)
    (DyadicUpper.value d.inputMagnitude) (DyadicUpper.value d.weightMagnitude) d.bounds (h.ranges j hj) he
    (DyadicUpper.nonnegative E) (h.activation j hj) (h.weight j hj) h.inputMagnitude (h.weightMagnitude j hj)
  exact hp.2.2.trans (hu.trans (projection_sound l.width true _ _ _ _ _ d.bounds))

structure VocabularyConditions (qw qi rw ri : ByteArray) (d : ProjectionData) : Prop where
  ranges : VocabularyPair.Ranges qw qi rw ri (ProjectionRangeCertificate.vocabularyParameters qw qi d.bounds)
  activation : ∀ i < 768, 0 ≤ ProjectionRangeCertificate.activationError qi 768 i ∧
    ProjectionRangeCertificate.activationError qi 768 i ≤ DyadicUpper.value d.activationError
  weight : ∀ j < 50257, 0 ≤ ProjectionRangeCertificate.weightError qw ProjectionRangeCertificate.vocabularyLayout j ∧
    ProjectionRangeCertificate.weightError qw ProjectionRangeCertificate.vocabularyLayout j ≤ DyadicUpper.value d.weightError
  inputMagnitude : ∀ i < 768, |ProjectionPair.inputValues ri i| ≤ DyadicUpper.value d.inputMagnitude
  weightMagnitude : ∀ j < 50257, ∀ i < 768, |VocabularyPair.weights rw j i| ≤ DyadicUpper.value d.weightMagnitude

theorem vocabulary_close (qw qi rw ri : ByteArray) (d : ProjectionData)
    (h : VocabularyConditions qw qi rw ri d) (E : Nat) (he : Close qi ri 768 (DyadicUpper.value E)) :
    Close (Quantized.linearGroupedRows qw qi VocabularyPair.layout.qWeight VocabularyPair.layout.qScale 0 768 50257 1 false)
      (vocabularyHead rw ri) 50257
      (DyadicUpper.value (project 768 false d E)) := by
  intro j hj
  have hp := VocabularyPair.component_error qw qi rw ri (DyadicUpper.value E)
    (ProjectionRangeCertificate.vocabularyParameters qw qi d.bounds) h.ranges he j hj
  have hu := ProjectionUniform.vocabulary_error_upper qw qi rw ri j
    (DyadicUpper.value E) (DyadicUpper.value d.activationError) (DyadicUpper.value d.weightError)
    (DyadicUpper.value d.inputMagnitude) (DyadicUpper.value d.weightMagnitude) d.bounds h.ranges hj he
    (DyadicUpper.nonnegative E) h.activation (h.weight j hj) h.inputMagnitude (h.weightMagnitude j hj)
  exact hp.2.2.trans (hu.trans (projection_sound 768 false _ _ _ _ _ d.bounds))

#print axioms learned_close
#print axioms vocabulary_close
end Project.Gpt2QuantizedCached.Numerical.ProjectionUpper
