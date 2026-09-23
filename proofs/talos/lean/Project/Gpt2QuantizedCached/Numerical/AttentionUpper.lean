import Project.Gpt2QuantizedCached.Numerical.OperationUpperSound
import Project.Gpt2QuantizedCached.Numerical.AttentionRange

namespace Project.Gpt2QuantizedCached.Numerical.AttentionUpper
open LeanExe.Models.Gpt2 Project.ProofKit Gpt2CachedStep OperationUpper

noncomputable def parameters (q r : CachedAttention.RangeCertificate.Parameters) : AttentionPair.Bounds :=
  ⟨CachedAttention.UniformError.bounds q.softmax.subtraction q.softmax.summation q.softmax.division q.valueMul q.valueAdd,
    CachedAttention.UniformError.bounds r.softmax.subtraction r.softmax.summation r.softmax.division r.valueMul r.valueAdd,
    fun _ => CachedScore.UniformError.bounds q.scoreMul q.scoreAdd q.scoreScale,
    fun _ => CachedScore.UniformError.bounds r.scoreMul r.scoreAdd r.scoreScale,
    DyadicUpper.value (DyadicUpper.fp32Magnitude q.valueMagnitude)⟩

theorem reference_score (qkv : ByteArray) (head : Nat) (K : Nat → ℝ) (m a s : Nat) :
    CachedScore.Error.error qkv head K (fun _ => 0) (fun _ => 0) (CachedScore.UniformError.bounds m a s) =
      CachedScore.UniformError.upper 0 0 0 0 m a s := by
  simp [CachedScore.Error.error, CachedScore.Error.dotError, CachedScore.UniformError.bounds, CachedScore.UniformError.upper]
  ring

structure Magnitudes (qq rc rq : ByteArray) (layer position Q K : Nat)
    (r : CachedAttention.RangeCertificate.Parameters) : Prop where
  query : ∀ head < 12, ∀ i < 64, |CodeLib.IEEE32.value (CachedScore.Error.query qq head i)| ≤ DyadicUpper.value Q
  key : ∀ head < 12, ∀ j < position + 1, ∀ i < 64,
    |CodeLib.IEEE32.value (CachedScore.Error.key rc rq layer position j head i)| ≤ DyadicUpper.value K
  value : ∀ i < 768, ∀ j < position + 1,
    |CodeLib.IEEE32.value (CachedAttention.ForwardError.valueWords rc rq layer position i j)| ≤
      DyadicUpper.value (DyadicUpper.fp32Magnitude r.valueMagnitude)

theorem close (qc qq rc rq : ByteArray) (layer position Q K E C : Nat) (hl : layer < 12)
    (q r : CachedAttention.RangeCertificate.Parameters)
    (h : Attention.Ranges qc qq rc rq layer position (fun _ => parameters q r))
    (hm : Magnitudes qq rc rq layer position Q K r)
    (hc : Close qc rc (position * 18432) (DyadicUpper.value C))
    (he : Close qq rq 2304 (DyadicUpper.value E)) :
    Close (cachedAttention qc qq layer position) (cachedAttention rc rq layer position) 768
      (DyadicUpper.value (attention position Q K E C q r)) := by
  let H := max E C
  let S := DyadicUpper.add (score Q K E H q.scoreMul q.scoreAdd q.scoreScale)
    (score 0 0 0 0 r.scoreMul r.scoreAdd r.scoreScale)
  have hh : max (DyadicUpper.value C) (DyadicUpper.value E) = DyadicUpper.value H := by
    rw [DyadicUpper.max_value, max_comm]
  intro i hi
  have hi' : i / 64 < 12 := by omega
  have hs (j : Nat) (hj : j < position + 1) :
      AttentionPair.scoreError qc qq rc rq layer position (i / 64) j (DyadicUpper.value C) (DyadicUpper.value E)
        (parameters q r) ≤ DyadicUpper.value S := by
    have hq := CachedScore.UniformError.error_upper qq (i / 64)
      (fun c => CodeLib.IEEE32.value (CachedScore.Error.key rc rq layer position j (i / 64) c))
      (DyadicUpper.value Q) (DyadicUpper.value K) (DyadicUpper.value E) (DyadicUpper.value H)
      q.scoreMul q.scoreAdd q.scoreScale (hm.query _ hi') (hm.key _ hi' j hj)
      (DyadicUpper.nonnegative E) (DyadicUpper.nonnegative H)
    have hqu := hq.trans (score_sound Q K E H q.scoreMul q.scoreAdd q.scoreScale)
    have hr := score_sound 0 0 0 0 r.scoreMul r.scoreAdd r.scoreScale
    simp only [DyadicUpper.value, Nat.cast_zero, zero_div] at hr
    unfold AttentionPair.scoreError
    dsimp only [parameters]
    rw [hh, reference_score]
    exact DyadicUpper.add_bound _ _ _ _ hqu hr
  have hp := AttentionPair.component_error qc qq rc rq layer position i hl hi
    (DyadicUpper.value C) (DyadicUpper.value E) (DyadicUpper.value S) (parameters q r) (h i hi)
    hc he (DyadicUpper.nonnegative S) hs
  have hq := CachedAttention.UniformError.rounding_upper qc qq layer position i
    (DyadicUpper.value (DyadicUpper.fp32Magnitude q.valueMagnitude)) q.softmax.subtraction q.softmax.summation q.softmax.division
    q.valueMul q.valueAdd (h i hi).quantized (fun j hj => (h i hi).valueMagnitude ⟨j, hj⟩)
  have hr := CachedAttention.UniformError.rounding_upper rc rq layer position i
    (DyadicUpper.value (DyadicUpper.fp32Magnitude r.valueMagnitude)) r.softmax.subtraction r.softmax.summation r.softmax.division
    r.valueMul r.valueAdd (h i hi).reference (hm.value i hi)
  have hqu := hq.trans (attentionRound_sound (position + 1) _ _ _ _ _ _)
  have hru := hr.trans (attentionRound_sound (position + 1) _ _ _ _ _ _)
  have hm' := times_bound _ _ 2 (DyadicUpper.mul_upper (DyadicUpper.fp32Magnitude q.valueMagnitude) S)
  have hm'' : 2 * DyadicUpper.value (DyadicUpper.fp32Magnitude q.valueMagnitude) * DyadicUpper.value S ≤
      DyadicUpper.value (2 * DyadicUpper.mul (DyadicUpper.fp32Magnitude q.valueMagnitude) S) := by
    simpa only [mul_assoc, Nat.cast_ofNat] using hm'
  apply hp.2.2.trans
  unfold AttentionPair.error
  dsimp only [parameters]
  rw [hh]
  exact DyadicUpper.add_bound _ _ _ _ (DyadicUpper.add_bound _ _ _ _ hqu
    (DyadicUpper.add_bound _ _ _ _ hm'' le_rfl)) hru

#print axioms close
end Project.Gpt2QuantizedCached.Numerical.AttentionUpper
