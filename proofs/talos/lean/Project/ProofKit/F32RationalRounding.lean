import Project.ProofKit.F32Rounding

namespace Project.ProofKit.F32RationalRounding
open Float.Model.UnpackedFloat F32Rounding

theorem initial_mantissa (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).mantissa = m := by
  cases acc with
  | exact => rfl
  | inexact o => cases o <;> rfl

theorem initial_rounded (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).roundedMantissa = acc.roundToNearestEven m := by
  cases acc with
  | exact => rfl
  | inexact o => cases o <;> rfl

theorem fraction_residual (m n d : Nat) :
    let em := ExtendedMantissa.ofMantissaAndAccuracy m (accuracyOfFraction n d)
    (em.roundBit || em.stickyBit) = (n != 0) := by
  by_cases hn : n = 0
  · simp [accuracyOfFraction, hn, ExtendedMantissa.ofMantissaAndAccuracy]
  · simp only [accuracyOfFraction, hn, ite_false]
    cases compare (2 * n) d <;> simp [ExtendedMantissa.ofMantissaAndAccuracy, hn]

theorem fraction_round (n d : Nat) (hd : 0 < d) :
    (accuracyOfFraction (n % d) d).roundToNearestEven (n / d) = Wasm.IEEE32.roundQuotient n d := by
  have hd0 : d ≠ 0 := by omega
  have hq := Nat.mod_lt (n / d) (by decide : 0 < 2)
  by_cases hr : n % d = 0
  · simp [accuracyOfFraction, hr, Accuracy.roundToNearestEven, Wasm.IEEE32.roundQuotient, hd0, hd]
  · simp only [accuracyOfFraction, hr, ite_false, Wasm.IEEE32.roundQuotient,
      beq_iff_eq, hd0]
    by_cases hl : 2 * (n % d) < d
    · rw [Nat.compare_eq_lt.mpr hl]
      simp [Accuracy.roundToNearestEven, hl]
    · by_cases hg : d < 2 * (n % d)
      · rw [Nat.compare_eq_gt.mpr hg]
        simp [Accuracy.roundToNearestEven, hl, hg]
      · have he : 2 * (n % d) = d := by omega
        rw [he]
        rw [Nat.compare_eq_eq.mpr rfl]
        simp only [Accuracy.roundToNearestEven, lt_self_iff_false, ite_false]
        by_cases hq0 : n / d % 2 = 0
        · simp [hq0]
        · have hq1 : n / d % 2 = 1 := by omega
          simp [hq1]

theorem shiftRightOne_fraction (n d : Nat) (hd : 0 < d) :
    (ExtendedMantissa.ofMantissaAndAccuracy (n / d) (accuracyOfFraction (n % d) d)).shiftRightOne =
      ExtendedMantissa.ofMantissaAndAccuracy (n / (d * 2)) (accuracyOfFraction (n % (d * 2)) (d * 2)) := by
  have hr := Nat.mod_lt n hd
  have hb := Nat.mod_lt (n / d) (by decide : 0 < 2)
  have hm : n % (d * 2) = n % d + d * (n / d % 2) := Nat.mod_mul
  simp only [ExtendedMantissa.shiftRightOne, initial_mantissa, fraction_residual,
    Nat.div_div_eq_div_mul]
  by_cases hb0 : n / d % 2 = 0
  · by_cases hr0 : n % d = 0
    · simp [hm, hb0, hr0, accuracyOfFraction, ExtendedMantissa.ofMantissaAndAccuracy]
    · have hc : compare (2 * (n % d)) (d * 2) = .lt := Nat.compare_eq_lt.mpr (by omega)
      simp [hm, hb0, hr0, accuracyOfFraction, hc, ExtendedMantissa.ofMantissaAndAccuracy]
  · have hb1 : n / d % 2 = 1 := by omega
    by_cases hr0 : n % d = 0
    · simp [hm, hb1, hr0, accuracyOfFraction, Nat.ne_of_gt hd, Nat.mul_comm,
        ExtendedMantissa.ofMantissaAndAccuracy]
    · have hc : compare (2 * (n % d + d)) (d * 2) = .gt := Nat.compare_eq_gt.mpr (by omega)
      simp [hm, hb1, hr0, accuracyOfFraction, hc, ExtendedMantissa.ofMantissaAndAccuracy]

theorem shift_fraction (n d k : Nat) (hd : 0 < d) :
    ExtendedMantissa.ofMantissaAndAccuracy (n / d) (accuracyOfFraction (n % d) d) >>> k =
      ExtendedMantissa.ofMantissaAndAccuracy (n / (d * 2 ^ k))
        (accuracyOfFraction (n % (d * 2 ^ k)) (d * 2 ^ k)) := by
  induction k with
  | zero => simp [shift_zero]
  | succ k ih =>
    rw [shift_succ, ih, shiftRightOne_fraction n (d * 2 ^ k) (by positivity)]
    simp [pow_succ, Nat.mul_assoc]

theorem rounded_fraction (n d k : Nat) (hd : 0 < d) :
    (ExtendedMantissa.ofMantissaAndAccuracy (n / d) (accuracyOfFraction (n % d) d) >>> k).roundedMantissa =
      Wasm.IEEE32.roundQuotient n (d * 2 ^ k) := by
  rw [shift_fraction n d k hd, initial_rounded, fraction_round n _ (by positivity)]

#print axioms fraction_round
#print axioms shiftRightOne_fraction
#print axioms rounded_fraction

end Project.ProofKit.F32RationalRounding
