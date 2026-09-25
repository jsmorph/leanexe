import Project.Gpt2CachedStep.GeluRangeCheck
import Project.Gpt2CachedStep.GeluForwardError
import Project.Gpt2CachedStep.ExpNeg.RangeCertificate

namespace Project.Gpt2CachedStep.GeluRangeCertificate
open Project.ProofKit

noncomputable def bounds (p : Parameters) : GeluForwardError.Bounds :=
  ⟨⟨p.square, p.weighted, p.factor, p.product, p.magnitude⟩,
    fun _ => p.exponential.multiplication, fun _ => p.exponential.addition,
    fun _ => p.exponential.squaring, p.denominatorAdd, p.numeratorMul,
    p.positiveDiv, p.negativeDiv, 1⟩

theorem inner_sound (a : UInt32) (p : Parameters) (h : checkInner a p = true) :
    GeluForwardError.Ranges a (bounds p) := by
  simp only [checkInner, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hs, hw, hf, hp, hm, he, hd, hl, hn, hPos, hNeg⟩ := h
  have hLower := F32RangeCertificate.lowerAbsolute_sound (GeluError.denominator a) 1 1 hl
  simp only [Nat.cast_one, div_one] at hLower
  simp only [F32RangeCertificate.multiplication, F32RangeCertificate.addition,
    F32RangeCertificate.division, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, and_assoc]
      at hs hw hf hp hm hd hn hPos hNeg
  exact {
    argument := ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2,
      hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2, hf.2.2.1, hf.2.2.2,
      hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
    expCutoff := ExpNeg.RangeCertificate.cutoff _ _ he
    expRanges := ExpNeg.RangeCertificate.sound _ _ he
    denominatorUpper := hd.2.2.1
    denominatorRange := hd.2.2.2
    lowerPositive := by norm_num [bounds]
    denominatorLower := hLower.2
    denominatorNonzero := hPos.2.2.2.2.1
    numeratorLower := hn.2.2.1
    numeratorUpper := hn.2.2.2.1
    numeratorRange := hn.2.2.2.2
    positiveLower := hPos.2.2.1
    positiveUpper := hPos.2.2.2.1
    positiveRange := hPos.2.2.2.2.2
    negativeLower := hNeg.2.2.1
    negativeUpper := hNeg.2.2.2.1
    negativeRange := hNeg.2.2.2.2.2 }

theorem sound (input : UInt32) (p : Parameters) (h : check input p = true) :
    CodeLib.IEEE32.Finite input ∧
      (¬F32Order.absBits input > 0x41000000 → GeluForwardError.Ranges (F32Order.absBits input) (bounds p)) := by
  simp only [check, Bool.and_eq_true] at h
  refine ⟨h.1, fun hi => ?_⟩
  have hc : (if F32Order.absBits input > 0x41000000 then true else checkInner (F32Order.absBits input) p) = true := h.2
  exact inner_sound _ _ (by simpa only [hi, ite_false] using hc)

#print axioms inner_sound
#print axioms sound
end Project.Gpt2CachedStep.GeluRangeCertificate
