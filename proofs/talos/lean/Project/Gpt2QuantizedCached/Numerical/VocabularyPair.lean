import LeanExe.Models.Gpt2.Quantized.Format
import Project.Gpt2QuantizedCached.Numerical.ProjectionPair
import Project.Gpt2QuantizedCached.Numerical.TensorBounds

namespace Project.Gpt2QuantizedCached.Numerical.VocabularyPair
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

def layout : ProjectionPair.Layout :=
  ⟨Quantized.tokenWeightOffset, Quantized.tokenScaleOffset, 0, 0, 0, 768, 50257⟩

structure Parameters where
  quantized : Nat → Gpt2QuantizedGroupedRows.OutputError.Bounds
  reference : Nat → F32DotError.Bounds
  activationError : Nat → Nat → ℝ
  weightError : Nat → Nat → ℝ

noncomputable def weights (rw : ByteArray) (token : Nat) : Nat → ℝ := fun i => value (word rw (token * 768 + i))

structure Ranges (qw qi rw ri : ByteArray) (p : Parameters) : Prop where
  quantized : ∀ j < 50257, Gpt2QuantizedGroupedRows.OutputError.Ranges qw qi layout.qWeight layout.qScale 0 768 j false
    (ProjectionPair.inputValues qi) (weights rw j) (p.activationError j) (p.weightError j) (p.quantized j)
  reference : ∀ j < 50257, F32DotError.Ranges (word ri) (fun i => word rw (j * 768 + i)) 768 (p.reference j)

noncomputable def componentError (qw qi rw ri : ByteArray) (inputError : ℝ) (p : Parameters) (token : Nat) : ℝ :=
  Gpt2QuantizedGroupedRows.OutputError.error qw qi layout.qWeight 768 token false (ProjectionPair.inputValues ri)
    (weights rw token) (fun i => p.activationError token i + inputError) (p.weightError token) (p.quantized token) +
      F32DotError.errorBound (word ri) (weights rw token) (fun _ => 0) (fun _ => 0) 768 (p.reference token)

noncomputable def error (qw qi rw ri : ByteArray) (inputError : ℝ) (p : Parameters) : ℝ :=
  FiniteErrorBound.upper (componentError qw qi rw ri inputError p) 50257

theorem component_error (qw qi rw ri : ByteArray) (inputError : ℝ) (p : Parameters)
    (h : Ranges qw qi rw ri p) (he : Close qi ri 768 inputError) (token : Nat) (ht : token < 50257) :
    CodeLib.IEEE32.Finite (word (Quantized.linearGroupedRows qw qi layout.qWeight layout.qScale 0 768 50257 1 false) token) ∧
      CodeLib.IEEE32.Finite (word (vocabularyHead rw ri) token) ∧
      |value (word (Quantized.linearGroupedRows qw qi layout.qWeight layout.qScale 0 768 50257 1 false) token) -
        value (word (vocabularyHead rw ri) token)| ≤ componentError qw qi rw ri inputError p token := by
  have hx := ProjectionPair.transfer_input qw qi layout token false (ProjectionPair.inputValues qi)
    (ProjectionPair.inputValues ri) (weights rw token) (p.activationError token) (fun _ => inputError)
    (p.weightError token) (p.quantized token) (h.quantized token ht) he
  have hq := Gpt2QuantizedGroupedRows.OutputError.output_error qw qi layout.qWeight layout.qScale 0 768 50257 token
    false ht (by decide) (ProjectionPair.inputValues ri) (weights rw token) (fun i => p.activationError token i + inputError)
    (p.weightError token) (p.quantized token) hx
  have hr := F32DotError.error_of_ranges (word ri) (fun i => word rw (token * 768 + i))
    (ProjectionPair.inputValues ri) (weights rw token) (fun _ => 0) (fun _ => 0) 768 (p.reference token)
    (h.reference token ht) (by intro i hi; simp [ProjectionPair.inputValues]) (by intro i hi; simp [weights])
  simp only [Gpt2QuantizedGroupedRows.OutputError.reference, Bool.false_eq_true, ite_false, add_zero] at hq
  rw [Gpt2LinearRows.Error.vocabulary_source rw ri token ht]
  exact ⟨hq.1, hr.1, F32ErrorPropagation.compare _ _ _ _ _ hq.2 hr.2⟩

theorem close (qw qi rw ri : ByteArray) (inputError : ℝ) (p : Parameters)
    (h : Ranges qw qi rw ri p) (he : Close qi ri 768 inputError) :
    Close (Quantized.linearGroupedRows qw qi layout.qWeight layout.qScale 0 768 50257 1 false)
      (vocabularyHead rw ri) 50257 (error qw qi rw ri inputError p) := by
  intro i hi
  exact (component_error qw qi rw ri inputError p h he i hi).2.2.trans
    (FiniteErrorBound.component_le (componentError qw qi rw ri inputError p) _ i hi)

#print axioms component_error
#print axioms close
end Project.Gpt2QuantizedCached.Numerical.VocabularyPair
