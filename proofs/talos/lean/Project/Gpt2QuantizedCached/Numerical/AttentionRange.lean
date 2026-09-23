import Project.Gpt2QuantizedCached.Numerical.AttentionPair
import Project.Gpt2CachedStep.CachedAttention.RangeCertificate

namespace Project.Gpt2QuantizedCached.Numerical.AttentionRange
open Project.Gpt2CachedStep.CachedAttention

noncomputable def parameters (qp rp : RangeCertificate.Parameters) : AttentionPair.Bounds :=
  ⟨RangeCertificate.bounds qp, RangeCertificate.bounds rp,
    fun _ => RangeCertificate.scoreBounds qp, fun _ => RangeCertificate.scoreBounds rp,
    (qp.valueMagnitude : ℝ) / 2 ^ 149⟩

theorem sound (qc qq rc rq : ByteArray) (layer position : Nat) (qp rp : RangeCertificate.Parameters)
    (hq : RangeCertificate.check qc qq layer position qp = true)
    (hr : RangeCertificate.check rc rq layer position rp = true) (i : Nat) (hi : i < 768) :
    AttentionPair.Ranges qc qq rc rq layer position i (parameters qp rp) := by
  have hQ := RangeCertificate.sound qc qq layer position qp hq
  have hR := RangeCertificate.sound rc rq layer position rp hr
  exact ⟨hQ.2.1 i hi, hR.2.1 i hi,
    fun j hj => hQ.1 j hj (i / 64) (by omega),
    fun j hj => hR.1 j hj (i / 64) (by omega),
    by dsimp only [parameters]; positivity,
    fun j => hQ.2.2 i hi j j.isLt⟩

#print axioms sound
end Project.Gpt2QuantizedCached.Numerical.AttentionRange
