import Project.Gpt2CachedStep.CachedAttention.SoftmaxRangeCheck
import Project.Gpt2CachedStep.CachedAttention.SoftmaxError
import Project.Gpt2CachedStep.ExpNeg.RangeCertificate
import Project.ProofKit.F32SumRangeCertificate

namespace Project.Gpt2CachedStep.CachedAttention.SoftmaxRangeCertificate
open Project.ProofKit CodeLib.IEEE32

noncomputable def bounds (p : Parameters) : SoftmaxError.Bounds :=
  ⟨fun _ => p.subtraction, fun _ => p.summation, fun _ => p.division,
    fun _ _ => p.exponential.multiplication, fun _ _ => p.exponential.addition,
    fun _ _ => p.exponential.squaring, 1⟩

theorem sound (scores : Nat → UInt32) (maximum : UInt32) (n : Nat) (p : Parameters)
    (h : check scores maximum n p = true) : SoftmaxError.Ranges scores maximum (bounds p) n := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨hf, hu, hs, hl, hn, hc⟩ := h
  have hLower := F32RangeCertificate.lowerAbsolute_sound _ 1 1 hl
  simp only [Nat.cast_one, div_one] at hLower
  have hSub (i : Nat) (hi : i < n) := (hc i hi).2.2.1
  have hDiv (i : Nat) (hi : i < n) := (hc i hi).2.2.2.2.2
  simp only [F32RangeCertificate.subtraction, F32RangeCertificate.division,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, and_assoc] at hSub hDiv
  refine {
    scoreFinite := fun i hi => (hc i hi).1
    maximumFinite := hf
    maximumUpper := ?_
    subUpper := fun i hi => (hSub i hi).2.2.1
    subRange := fun i hi => (hSub i hi).2.2.2
    shiftedNonpositive := ?_
    cutoff := fun i hi => ExpNeg.RangeCertificate.cutoff _ _ (hc i hi).2.2.2.2.1
    expRanges := fun i hi => ExpNeg.RangeCertificate.sound _ _ (hc i hi).2.2.2.2.1
    sumUpper := fun _ _ => hu
    sumRange := F32SumRangeCertificate.ranges _ _ _ hs
    lowerPositive := by norm_num [bounds]
    denominatorLower := hLower.2
    denominatorNonzero := hn
    divLower := fun i hi => (hDiv i hi).2.2.1
    divUpper := fun i hi => (hDiv i hi).2.2.2.1
    divRange := fun i hi => (hDiv i hi).2.2.2.2.2 }
  · intro i hi
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (hc i hi).2.1
  · intro i hi
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact_mod_cast (hc i hi).2.2.2.1

#print axioms sound
end Project.Gpt2CachedStep.CachedAttention.SoftmaxRangeCertificate
