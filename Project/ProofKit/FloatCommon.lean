import Project.ProofKit.FloatShift
import CodeLib.IEEE32.Roundoff

/-!
Lemmas about Lean's float model and the exact rounding helpers that hold for
both binary32 and binary64.
-/

namespace Project.ProofKit.FloatCommon
open Float.Model Float.Model.UnpackedFloat FloatRounding FloatShift

theorem append_toNat (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

def negative (s : Sign) : Bool := match s with
  | .negative => true
  | .positive => false

def aligned (m : Nat) (e target : Int) : ExtendedMantissa :=
  ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ (e - target).toNat) .exact >>>
    (target - e).toNat

theorem aligned_mul_pow (m k : Nat) (e t : Int) :
    aligned (m * 2 ^ k) (e - k) t = aligned m e t := by
  by_cases hte : t ≤ e - k
  · have hl : (t - (e - k)).toNat = 0 := by omega
    have hr : (t - e).toNat = 0 := by omega
    have hk : k + (e - k - t).toNat = (e - t).toNat := by omega
    simp only [aligned, hl, hr, shift_zero]
    rw [Nat.mul_assoc, ← pow_add, hk]
  · have hl : (e - k - t).toNat = 0 := by omega
    simp only [aligned, hl, pow_zero, Nat.mul_one]
    by_cases hte' : t ≤ e
    · have hr : (t - e).toNat = 0 := by omega
      have hk : (t - (e - k)).toNat ≤ k := by omega
      have he : k - (t - (e - k)).toNat = (e - t).toNat := by omega
      rw [hr, shift_zero, shift_exact_mul_pow_le m k _ hk, he]
    · have hr : (e - t).toNat = 0 := by omega
      have hk : (t - (e - k)).toNat = k + (t - e).toNat := by omega
      rw [hk, shift_exact_mul_pow_add, hr]
      simp

theorem sign_apply_mul (s : Sign) (m n : Nat) :
    s.apply (m : Int) * (n : Int) = s.apply ((m * n : Nat) : Int) := by
  cases s <;> simp [Sign.apply]

theorem sign_apply_neg (s : Sign) (z : Int) : (-s).apply z = -(s.apply z) := by
  cases s with
  | negative => exact (neg_neg z).symm
  | positive => rfl

def rounded (m k : Nat) : Nat := if k = 0 then m else Wasm.IEEE32.roundShift m k

theorem rounded_eq (m k : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> k).roundedMantissa = rounded m k := by
  cases k with
  | zero => rfl
  | succ k => exact round_exact_shift m k

theorem rounded_bounds (m k : Nat) : m / 2 ^ k ≤ rounded m k ∧ rounded m k ≤ m / 2 ^ k + 1 := by
  by_cases hk : k = 0
  · simp [rounded, hk]
  · simpa [rounded, hk] using CodeLib.IEEE32.roundShift_bounds m k

theorem negative_mul (a b : Sign) : negative (a * b) = (negative a != negative b) := by
  cases a <;> cases b <;> rfl

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

theorem negative_div (a b : Sign) : negative (a / b) = (negative a != negative b) := by
  cases a <;> cases b <;> rfl

end Project.ProofKit.FloatCommon
