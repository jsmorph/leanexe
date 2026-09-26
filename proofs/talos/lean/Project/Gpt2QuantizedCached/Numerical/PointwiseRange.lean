import Project.Gpt2QuantizedCached.Numerical.PointwiseRangeCheck
import Project.Gpt2QuantizedCached.Numerical.ProjectionRange
import Project.Gpt2QuantizedCached.Numerical.EmbeddingPair

namespace Project.Gpt2QuantizedCached.Numerical.PointwiseRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

noncomputable def embeddingParameters (qw : ByteArray) (token : UInt32) (p : EmbeddingParameters) : EmbeddingPair.Parameters :=
  ⟨fun _ => p.multiplication, fun _ => p.quantizedAdd, fun _ => p.referenceAdd,
    fun _ => ProjectionRangeCertificate.weightError qw ProjectionRangeCertificate.vocabularyLayout token.toNat⟩

theorem embedding_sound (qw rw : ByteArray) (token : UInt32) (position : Nat) (p : EmbeddingParameters)
    (h : checkEmbedding qw rw token position p = true) (he : Export.check rw qw = true)
    (ht : token.toNat < 50257) :
    EmbeddingPair.Ranges qw rw token position (embeddingParameters qw token p) := by
  simp only [checkEmbedding, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    beq_iff_eq, and_assoc] at h
  have hm (i : Nat) (hi : i < 768) := (h i hi).2.1
  have hq (i : Nat) (hi : i < 768) := (h i hi).2.2.1
  have hr (i : Nat) (hi : i < 768) := (h i hi).2.2.2.1
  simp only [F32RangeCertificate.multiplication, F32RangeCertificate.addition,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hm hq hr
  refine ⟨?_, ?_, fun i hi => (h i hi).2.2.2.2, fun i hi => (hr i hi).1,
    fun i hi => (hr i hi).2.1, fun i hi => (hr i hi).2.2.1, fun i hi => (hr i hi).2.2.2⟩
  · intro i hi
    exact ⟨(h i hi).1, (hm i hi).2.1, (hq i hi).2.1, (hm i hi).2.2.1,
      (hm i hi).2.2.2.1, (hm i hi).2.2.2.2, (hq i hi).2.2.1, (hq i hi).2.2.2⟩
  · intro i hi
    have hw := ProjectionRangeCertificate.exported_weight rw qw ProjectionRangeCertificate.vocabularyLayout
      token.toNat i he ProjectionRangeCertificate.vocabulary_member ht hi
    simp only [ProjectionRangeCertificate.weightWord, ProjectionRangeCertificate.vocabularyLayout,
      Nat.zero_add, Nat.mul_one] at hw
    exact hw

theorem add_sound (ql qr rl rr : ByteArray) (qb rb : Nat)
    (hq : checkAdd ql qr qb = true) (hr : checkAdd rl rr rb = true) :
    Add.Ranges ql qr rl rr 768 ⟨fun _ => qb, fun _ => rb⟩ := by
  simp only [checkAdd, List.all_eq_true, List.mem_range, F32RangeCertificate.addition,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hq hr
  intro i hi
  exact ⟨(hq i hi).1, (hq i hi).2.1, (hr i hi).1, (hr i hi).2.1,
    (hq i hi).2.2.1, (hr i hi).2.2.1, (hq i hi).2.2.2, (hr i hi).2.2.2⟩

#print axioms embedding_sound
#print axioms add_sound
end Project.Gpt2QuantizedCached.Numerical.PointwiseRangeCertificate
