import Project.Gpt2QuantizedCached.Numerical.OperationUpperSound
import Project.Gpt2QuantizedCached.Numerical.EmbeddingPair
import Project.Gpt2CachedStep.GeluUniform

namespace Project.Gpt2QuantizedCached.Numerical.PointwiseUpper
open LeanExe.Models.Gpt2 Project.ProofKit

theorem embedding_close (qw rw : ByteArray) (token : UInt32) (position D m a r : Nat)
    (p : EmbeddingPair.Parameters) (h : EmbeddingPair.Ranges qw rw token position p)
    (hm : ∀ i < 768, p.qMul i = m) (ha : ∀ i < 768, p.qAdd i = a)
    (hr : ∀ i < 768, p.rAdd i = r) (hd : ∀ i < 768, p.weightError i ≤ DyadicUpper.value D) :
    Close (Quantized.embedding qw token position) (Gpt2CachedStep.CachedHidden.embedding rw token position)
      768 (DyadicUpper.value (OperationUpper.embedding D m a r)) := by
  intro i hi
  apply (EmbeddingPair.component_error qw rw token position p h i hi).trans
  unfold EmbeddingPair.componentError
  rw [hm i hi, ha i hi, hr i hi]
  exact (add_le_add (add_le_add le_rfl (add_le_add le_rfl (hd i hi))) le_rfl).trans
    (OperationUpper.embedding_sound D m a r)

theorem residual_close (ql qr rl rr : ByteArray) (n L R q r : Nat)
    (h : Add.Ranges ql qr rl rr n ⟨fun _ => q, fun _ => r⟩)
    (hq : n ≤ ql.size / 4) (hr : n ≤ rl.size / 4)
    (hl : Close ql rl n (DyadicUpper.value L)) (hRight : Close qr rr n (DyadicUpper.value R)) :
    Close (addRows ql qr) (addRows rl rr) n (DyadicUpper.value (OperationUpper.residual L R q r)) := by
  intro i hi
  exact (PointwisePair.add_error ql qr rl rr i q r (by omega) (by omega) _ _ (h i hi) (hl i hi) (hRight i hi)).trans
    (OperationUpper.residual_sound L R q r)

theorem gelu_close (qi ri : ByteArray) (n E : Nat)
    (h : ∀ i < n, PointwisePair.GeluRanges qi ri i Gpt2CachedStep.GeluUniform.bounds Gpt2CachedStep.GeluUniform.bounds)
    (hq : n ≤ qi.size / 4) (hr : n ≤ ri.size / 4) (he : Close qi ri n (DyadicUpper.value E)) :
    Close (activate qi) (activate ri) n (DyadicUpper.value (OperationUpper.gelu E)) := by
  intro i hi
  have hp := h i hi
  have hq' := Gpt2CachedStep.GeluUniform.error_upper (word qi i) hp.qFinite hp.qRange
  have hr' := Gpt2CachedStep.GeluUniform.error_upper (word ri i) hp.rFinite hp.rRange
  have hu : Gpt2CachedStep.GeluForwardError.error (word qi i) Gpt2CachedStep.GeluUniform.bounds +
      4 * DyadicUpper.value E + Gpt2CachedStep.GeluForwardError.error (word ri i) Gpt2CachedStep.GeluUniform.bounds ≤
      1 / 8 + 4 * DyadicUpper.value E := by linarith
  exact (PointwisePair.gelu_error qi ri i (by omega) (by omega) _ _ _ hp (he i hi)).trans
    (hu.trans (OperationUpper.gelu_sound E))

#print axioms embedding_close
#print axioms residual_close
#print axioms gelu_close
end Project.Gpt2QuantizedCached.Numerical.PointwiseUpper
