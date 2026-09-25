import Project.Gpt2CachedStep.CachedAttention.RangeCheck
import Project.Gpt2CachedStep.CachedAttention.ForwardError
import Project.Gpt2CachedStep.CachedAttention.SoftmaxRangeCertificate
import Project.ProofKit.F32DotRangeCertificate

namespace Project.Gpt2CachedStep.CachedAttention.RangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

def scoreBounds (p : Parameters) : CachedScore.Error.Bounds :=
  ⟨fun _ => p.scoreMul, fun _ => p.scoreAdd, p.scoreScale⟩

noncomputable def bounds (p : Parameters) : ForwardError.Bounds :=
  ⟨SoftmaxRangeCertificate.bounds p.softmax, fun _ => p.valueMul, fun _ => p.valueAdd⟩

theorem score_sound (cache qkv : ByteArray) (layer position source head : Nat) (p : Parameters)
    (h : scoreCheck cache qkv layer position source head p = true) :
    CachedScore.Error.Ranges cache qkv layer position source head (scoreBounds p) := by
  simp only [scoreCheck, Bool.and_eq_true] at h
  have hd := F32DotRangeCertificate.ranges _ _ _ _ _ h.1
  have hs := h.2
  rw [F32DotRangeCertificate.prefix_value] at hs
  simp only [F32RangeCertificate.multiplication, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hs
  exact ⟨hd.inputFinite, hd.weightFinite, hd.mulLower, hd.mulUpper, hd.mulRange,
    hd.addUpper, hd.addRange, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

theorem sound (cache qkv : ByteArray) (layer position : Nat) (p : Parameters)
    (h : check cache qkv layer position p = true) :
    (∀ source < position + 1, ∀ head < 12,
      CachedScore.Error.Ranges cache qkv layer position source head (scoreBounds p)) ∧
    (∀ i < 768, ForwardError.Ranges cache qkv layer position i (bounds p)) ∧
    (∀ i < 768, ∀ j < position + 1,
      |value (ForwardError.valueWords cache qkv layer position i j)| ≤ (p.valueMagnitude : ℝ) / 2 ^ 149) := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  refine ⟨fun source hs head hh => score_sound _ _ _ _ _ _ _ ((h.1 head hh).1 source hs), ?_, ?_⟩
  · intro i hi
    have hd := F32DotRangeCertificate.ranges _ _ _ _ _ (h.2 i hi).1
    exact ⟨SoftmaxRangeCertificate.sound _ _ _ _ (h.1 (i / 64) (by omega)).2,
      hd.weightFinite, hd.mulLower, hd.mulUpper, hd.mulRange, hd.addUpper, hd.addRange⟩
  · intro i hi j hj
    rw [F32Order.abs_value_scaledMagnitude]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (h.2 i hi).2 j hj

#print axioms score_sound
#print axioms sound
end Project.Gpt2CachedStep.CachedAttention.RangeCertificate
