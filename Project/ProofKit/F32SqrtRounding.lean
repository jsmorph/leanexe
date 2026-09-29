import Project.ProofKit.F32RationalRounding
import Mathlib.Data.Nat.Sqrt

namespace Project.ProofKit.F32SqrtRounding
open Float.Model.UnpackedFloat F32RationalRounding

def rootAccuracy (n : Nat) : Accuracy :=
  let r := n.sqrt
  let rem := n - r * r
  if rem = 0 then .exact else .inexact (if rem ≤ r then .lt else .gt)

theorem rounded_root (n : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy n.sqrt (rootAccuracy n)).roundedMantissa =
      Wasm.IEEE32.roundSqrtIntegral n 0 := by
  have hs := Nat.sqrt_le n
  have he : n - n.sqrt * n.sqrt + n.sqrt * n.sqrt = n := Nat.sub_add_cancel hs
  rw [initial_rounded]
  by_cases hr : n - n.sqrt * n.sqrt ≤ n.sqrt
  · have hl : 4 * n < (2 * n.sqrt + 1) ^ 2 := by nlinarith
    simp only [Wasm.IEEE32.roundSqrtIntegral, pow_zero, Nat.div_one, Nat.mul_zero,
      Nat.mul_one, hl, ite_true]
    by_cases hz : n - n.sqrt * n.sqrt = 0
    · simp [rootAccuracy, hz, Accuracy.roundToNearestEven]
    · simp [rootAccuracy, hz, hr, Accuracy.roundToNearestEven]
  · have hg : (2 * n.sqrt + 1) ^ 2 < 4 * n := by nlinarith
    have hl : ¬4 * n < (2 * n.sqrt + 1) ^ 2 := by omega
    have hz : n - n.sqrt * n.sqrt ≠ 0 := by omega
    simp [rootAccuracy, hz, hr, Accuracy.roundToNearestEven,
      Wasm.IEEE32.roundSqrtIntegral, hl, hg]

theorem rounded_root_bounds (n : Nat) :
    n.sqrt ≤ Wasm.IEEE32.roundSqrtIntegral n 0 ∧
      Wasm.IEEE32.roundSqrtIntegral n 0 ≤ n.sqrt + 1 := by
  rw [← rounded_root, initial_rounded]
  by_cases hz : n - n.sqrt * n.sqrt = 0 <;>
    by_cases hl : n - n.sqrt * n.sqrt ≤ n.sqrt <;>
    simp [rootAccuracy, hz, hl, Accuracy.roundToNearestEven]

theorem sqrt_scaled_div (n c : Nat) (hc : 0 < c) : (n * (c * c)).sqrt / c = n.sqrt := by
  have hl := Nat.sqrt_le n
  have hu := Nat.lt_succ_sqrt n
  have hl' : n.sqrt * c ≤ (n * (c * c)).sqrt := by
    apply Nat.le_sqrt.mpr
    have := Nat.mul_le_mul_right (c * c) hl
    nlinarith
  have hu' : (n * (c * c)).sqrt < (n.sqrt + 1) * c := by
    apply Nat.sqrt_lt.mpr
    have := Nat.mul_lt_mul_of_pos_right hu (Nat.mul_pos hc hc)
    simp only [Nat.succ_eq_add_one] at this
    nlinarith
  have := (Nat.le_div_iff_mul_le hc).mpr hl'
  have := (Nat.div_lt_iff_lt_mul hc).mpr hu'
  omega

theorem sqrt_scaled_pow (n k : Nat) :
    (n * 2 ^ (2 * k)).sqrt / 2 ^ k = n.sqrt := by
  rw [show 2 * k = k + k by omega, pow_add]
  exact sqrt_scaled_div n (2 ^ k) (by positivity)

theorem roundSqrtIntegral_scaled (n k : Nat) :
    Wasm.IEEE32.roundSqrtIntegral (n * 2 ^ (2 * k)) k = Wasm.IEEE32.roundSqrtIntegral n 0 := by
  have hp : 0 < 2 ^ (2 * k) := by positivity
  simp only [Wasm.IEEE32.roundSqrtIntegral, sqrt_scaled_pow, pow_zero, Nat.div_one,
    Nat.mul_zero, Nat.mul_one]
  rw [show 4 * (n * 2 ^ (2 * k)) = (4 * n) * 2 ^ (2 * k) by ring]
  simp only [Nat.mul_lt_mul_right hp]

#print axioms rounded_root
#print axioms roundSqrtIntegral_scaled

end Project.ProofKit.F32SqrtRounding
