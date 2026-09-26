import Project.Beck.State

namespace Project.Beck.Move

open LeanExe.Examples.Beck

def distance (D p d : ℤ) : ℤ := if d < 0 then D + p else D - p

theorem bounds (D p d speed step : ℤ)
    (cube : |p| ≤ D) (speedPositive : 0 < speed) (stepNonnegative : 0 ≤ step)
    (limit : d ≠ 0 → step * |d| ≤ distance D p d * speed) :
    |p * speed + step * d| ≤ D * speed := by
  rw [abs_le] at cube ⊢
  rcases lt_trichotomy d 0 with negative | zero | positive
  · have h := limit (ne_of_lt negative)
    rw [abs_of_neg negative, distance, ite_eq_left negative] at h
    have lower := mul_le_mul_of_nonneg_right cube.1 (le_of_lt speedPositive)
    have upper := mul_le_mul_of_nonneg_right cube.2 (le_of_lt speedPositive)
    have sign := mul_nonpos_of_nonneg_of_nonpos stepNonnegative (le_of_lt negative)
    constructor <;> nlinarith
  · subst d
    constructor
    · simpa using mul_le_mul_of_nonneg_right cube.1 (le_of_lt speedPositive)
    · simpa using mul_le_mul_of_nonneg_right cube.2 (le_of_lt speedPositive)
  · have h := limit (ne_of_gt positive)
    rw [abs_of_pos positive, distance, ite_eq_right (not_lt_of_gt positive)] at h
    have lower := mul_le_mul_of_nonneg_right cube.1 (le_of_lt speedPositive)
    have upper := mul_le_mul_of_nonneg_right cube.2 (le_of_lt speedPositive)
    have sign := mul_nonneg stepNonnegative (le_of_lt positive)
    constructor <;> nlinarith

theorem hits (D p d : ℤ) (hD : 0 ≤ D) :
    |p * |d| + distance D p d * d| = D * |d| := by
  rcases lt_trichotomy d 0 with negative | zero | positive
  · rw [abs_of_neg negative, distance, ite_eq_left negative]
    have same : p * -d + (D + p) * d = D * d := by ring
    rw [same, abs_mul, abs_of_nonneg hD, abs_of_neg negative]
  · simp [zero, distance]
  · rw [abs_of_pos positive, distance, ite_eq_right (not_lt_of_gt positive)]
    have same : p * d + (D - p) * d = D * d := by ring
    rw [same, abs_mul, abs_of_nonneg hD, abs_of_pos positive]

end Project.Beck.Move
