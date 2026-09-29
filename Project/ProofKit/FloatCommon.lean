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

end Project.ProofKit.FloatCommon
