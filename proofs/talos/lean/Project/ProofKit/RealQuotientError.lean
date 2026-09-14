import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Project.ProofKit.RealQuotientError

theorem denominator_error (a b B error : ℝ) (hb : b ≠ 0) (hB : B ≠ 0)
    (he : |b - B| ≤ error) :
    |a / b - a / B| ≤ |a| * error / (|b| * |B|) := by
  have hid : a / b - a / B = (-a) * (b - B) / (b * B) := by
    field_simp
    ring
  rw [hid, abs_div, abs_mul, abs_neg, abs_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (abs_nonneg a)) (mul_nonneg (abs_nonneg b) (abs_nonneg B))

#print axioms denominator_error
end Project.ProofKit.RealQuotientError
