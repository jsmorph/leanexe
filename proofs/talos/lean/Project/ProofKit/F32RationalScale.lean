import Project.ProofKit.F32RoundRational
import Project.ProofKit.F32Shift

namespace Project.ProofKit.F32RationalScale
open Float.Model Float.Model.UnpackedFloat F32RationalRounding F32RoundScaled

theorem accuracy_mul (n d c : Nat) (hc : 0 < c) :
    accuracyOfFraction (n * c) (d * c) = accuracyOfFraction n d := by
  have hc0 : c ≠ 0 := by omega
  by_cases hn : n = 0
  · simp [accuracyOfFraction, hn]
  · simp only [accuracyOfFraction, Nat.mul_eq_zero, hn, hc0, or_self, ite_false]
    congr 1
    by_cases hl : 2 * n < d
    · rw [Nat.compare_eq_lt.mpr hl, Nat.compare_eq_lt.mpr (by nlinarith)]
    · by_cases hg : d < 2 * n
      · rw [Nat.compare_eq_gt.mpr hg, Nat.compare_eq_gt.mpr (by nlinarith)]
      · have he : 2 * n = d := by omega
        rw [Nat.compare_eq_eq.mpr he, Nat.compare_eq_eq.mpr (by nlinarith)]

theorem initial_mul (n d c : Nat) (hc : 0 < c) :
    ExtendedMantissa.ofMantissaAndAccuracy (n * c / (d * c))
      (accuracyOfFraction ((n * c) % (d * c)) (d * c)) =
      ExtendedMantissa.ofMantissaAndAccuracy (n / d) (accuracyOfFraction (n % d) d) := by
  rw [Nat.mul_div_mul_right _ _ hc, Nat.mul_mod_mul_right, accuracy_mul _ _ c hc]

theorem quotient_log_mul_pow (n d k : Nat) (hd : 0 < d) (hq : n / d ≠ 0) :
    (n * 2 ^ k / d).log2 = (n / d).log2 + k := by
  have hl := Nat.log2_self_le hq
  have hu : n / d < 2 ^ ((n / d).log2 + 1) := Nat.lt_log2_self
  have hl' := (Nat.le_div_iff_mul_le hd).mp hl
  have hu' := (Nat.div_lt_iff_lt_mul hd).mp hu
  have hlo : 2 ^ ((n / d).log2 + k) ≤ n * 2 ^ k / d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    rw [pow_add]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ k) hl'
  have hhi : n * 2 ^ k / d < 2 ^ ((n / d).log2 + k + 1) := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have hp : 0 < 2 ^ k := by positivity
    rw [show (n / d).log2 + k + 1 = (n / d).log2 + 1 + k by omega, pow_add]
    nlinarith
  apply (Nat.log2_eq_iff (by have := Nat.two_pow_pos ((n / d).log2 + k); omega)).mpr
  exact ⟨hlo, hhi⟩

theorem quotient_log_mul_pow_zero (n d k : Nat) (hd : 0 < d) (hq : n / d = 0) :
    (n * 2 ^ k / d).log2 ≤ k := by
  have hn : n < d := by have := Nat.div_eq_zero_iff.mp hq; omega
  have h : n * 2 ^ k / d < 2 ^ k := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have hp : 0 < 2 ^ k := by positivity
    nlinarith
  by_cases hz : n * 2 ^ k / d = 0
  · simp [hz]
  · have := (Nat.log2_lt hz).mpr h
    omega

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

end Project.ProofKit.F32RationalScale
