import Project.ProofKit.F32Rounding

namespace Project.ProofKit.F32Shift
open Float.Model Float.Model.UnpackedFloat F32Rounding

theorem shift_add (em : ExtendedMantissa) (a b : Nat) :
    em >>> (a + b) = (em >>> a) >>> b := by
  induction b with
  | zero => simp [shift_zero]
  | succ b ih => rw [Nat.add_succ, shift_succ, ih, shift_succ]

theorem shift_exact_mul_pow (m k : Nat) :
    ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ k) .exact >>> k =
      ExtendedMantissa.ofMantissaAndAccuracy m .exact := by
  induction k generalizing m with
  | zero => simp [shift_zero]
  | succ k ih =>
    rw [pow_succ, show m * (2 ^ k * 2) = (m * 2) * 2 ^ k by ring,
      shift_succ, ih]
    simp [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.shiftRightOne]

theorem shift_exact_mul_pow_add (m a b : Nat) :
    ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ a) .exact >>> (a + b) =
      ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> b := by
  rw [shift_add, shift_exact_mul_pow]

theorem shift_exact_mul_pow_le (m a b : Nat) (h : b ≤ a) :
    ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ a) .exact >>> b =
      ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ (a - b)) .exact := by
  have ha : a = (a - b) + b := by omega
  conv_lhs => rw [ha, pow_add, ← Nat.mul_assoc]
  rw [shift_exact_mul_pow]

theorem log2_mul_pow (m k : Nat) (hm : m ≠ 0) :
    (m * 2 ^ k).log2 = m.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, show m * (2 ^ k * 2) = 2 * (m * 2 ^ k) by ring,
      Nat.log2_two_mul (Nat.mul_ne_zero hm (by positivity)), ih]
    omega

theorem target_mul_pow (m k : Nat) (e : Int) (hm : m ≠ 0) :
    Format.binary32.targetExponent (totalExponent (m * 2 ^ k) (e - k)) =
      Format.binary32.targetExponent (totalExponent m e) := by
  congr 1
  simp only [totalExponent, log2_mul_pow m k hm, Nat.cast_add]
  omega

#print axioms shift_exact_mul_pow_add
#print axioms target_mul_pow

end Project.ProofKit.F32Shift
