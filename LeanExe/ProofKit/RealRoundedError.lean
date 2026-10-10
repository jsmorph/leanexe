import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Errors of sums and products whose operands carry errors, and the magnitude of a value within a
relative error of another.
-/

namespace LeanExe.ProofKit.RealRoundedError

/-- The error of a product from the errors of its factors. -/
theorem factor_error (a b A B ea eb : ℝ)
    (ha : |a - A| ≤ ea) (hb : |b - B| ≤ eb) :
    |a * b - A * B| ≤ ea * |b| + |A| * eb := by
  calc
    _ = |(a - A) * b + A * (b - B)| := by congr 1; ring
    _ ≤ |(a - A) * b| + |A * (b - B)| := abs_add_le _ _
    _ = |a - A| * |b| + |A| * |b - B| := by rw [abs_mul, abs_mul]
    _ ≤ ea * |b| + |A| * eb :=
      add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))

theorem rounded_sum_error (c a b A B ec ea eb : ℝ)
    (hc : |c - (a + b)| ≤ ec) (ha : |a - A| ≤ ea) (hb : |b - B| ≤ eb) :
    |c - (A + B)| ≤ ec + ea + eb := by
  have hs : |a + b - (A + B)| ≤ ea + eb := by
    calc
      _ = |(a - A) + (b - B)| := by congr 1; ring
      _ ≤ |a - A| + |b - B| := abs_add_le _ _
      _ ≤ ea + eb := add_le_add ha hb
  calc
    _ ≤ |c - (a + b)| + |a + b - (A + B)| := abs_sub_le _ _ _
    _ ≤ ec + (ea + eb) := add_le_add hc hs
    _ = ec + ea + eb := by ring

theorem rounded_product_error (c a b A B ec ea eb : ℝ)
    (hc : |c - a * b| ≤ ec) (ha : |a - A| ≤ ea) (hb : |b - B| ≤ eb) :
    |c - A * B| ≤ ec + ea * |b| + |A| * eb := by
  calc
    _ ≤ |c - a * b| + |a * b - A * B| := abs_sub_le _ _ _
    _ ≤ ec + (ea * |b| + |A| * eb) := add_le_add hc (factor_error _ _ _ _ _ _ ha hb)
    _ = ec + ea * |b| + |A| * eb := by ring

/-- A value within relative error `u ≤ 1` of `A` has magnitude at most `2 |A|`. -/
theorem rel_bound {X A u : ℝ} (hu1 : u ≤ 1) (h : |X - A| ≤ u * |A|) : |X| ≤ 2 * |A| := by
  have h1 := abs_le.mp h
  have h2 : u * |A| ≤ |A| := mul_le_of_le_one_left (abs_nonneg A) hu1
  rw [abs_le]
  constructor <;> cases abs_cases A <;> linarith

#print axioms factor_error
#print axioms rounded_sum_error
#print axioms rounded_product_error
#print axioms rel_bound

end LeanExe.ProofKit.RealRoundedError
