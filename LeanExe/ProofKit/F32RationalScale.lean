import LeanExe.ProofKit.F32RoundRational
import LeanExe.ProofKit.FloatShift

namespace LeanExe.ProofKit.F32RationalScale
open Float.Model Float.Model.UnpackedFloat FloatRationalRounding F32RoundScaled FloatCommon

theorem target_mul_pow (n d k : Nat) (e : Int) (hd : 0 < d)
    (he : e ≤ Format.binary32.targetExponent (totalExponent (n / d) e)) :
    Format.binary32.targetExponent (totalExponent (n * 2 ^ k / d) (e - k)) =
      Format.binary32.targetExponent (totalExponent (n / d) e) := by
  by_cases hq : n / d = 0
  · have hl := quotient_log_mul_pow_zero n d k hd hq
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, hq, Nat.log2_zero] at he ⊢
    omega
  · simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, quotient_log_mul_pow n d k hd hq, Nat.cast_add]
    congr 1
    omega

theorem first_shift_mul_pow (n d k : Nat) (e : Int) (hd : 0 < d)
    (he : e ≤ Format.binary32.targetExponent (totalExponent (n / d) e)) :
    shiftToTargetExponent Format.binary32 (n * 2 ^ k / d) (e - k)
      (accuracyOfFraction ((n * 2 ^ k) % d) d) =
      shiftToTargetExponent Format.binary32 (n / d) e (accuracyOfFraction (n % d) d) := by
  let t := Format.binary32.targetExponent (totalExponent (n / d) e)
  have hk : (t - (e - k)).toNat = (t - e).toNat + k := by dsimp [t]; omega
  have heq : e - k + (t - (e - k)).toNat = e + (t - e).toNat := by omega
  simp only [shiftToTargetExponent, target_mul_pow n d k e hd he, shiftToExponent]
  change (_, e - k + (t - (e - k)).toNat) = (_, e + (t - e).toNat)
  rw [heq, shift_fraction _ d _ hd, shift_fraction _ d _ hd, hk, pow_add]
  rw [← Nat.mul_assoc, initial_mul _ _ _ (by positivity)]

theorem roundWithAccuracy_mul_pow (s : Sign) (n d k : Nat) (e : Int) (hd : 0 < d)
    (he : e ≤ Format.binary32.targetExponent (totalExponent (n / d) e)) :
    roundWithAccuracy Format.binary32 s (n * 2 ^ k / d) (e - k)
      (accuracyOfFraction ((n * 2 ^ k) % d) d) =
      roundWithAccuracy Format.binary32 s (n / d) e (accuracyOfFraction (n % d) d) := by
  unfold roundWithAccuracy
  rw [first_shift_mul_pow n d k e hd he]

#print axioms roundWithAccuracy_mul_pow

end LeanExe.ProofKit.F32RationalScale
