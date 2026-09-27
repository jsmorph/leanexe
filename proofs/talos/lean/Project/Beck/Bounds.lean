import Mathlib.Tactic

namespace Project.Beck.Bounds

theorem denominator_growth (bound round denominator speed : ℕ)
    (denominatorBound : denominator ≤ bound ^ round) (speedBound : speed ≤ bound) :
    denominator * speed ≤ bound ^ (round + 1) := by
  calc
    denominator * speed ≤ bound ^ round * bound := Nat.mul_le_mul denominatorBound speedBound
    _ = bound ^ (round + 1) := (pow_succ _ _).symm

theorem update_bounds (D p d speed distance bound : ℤ)
    (positive : 0 ≤ D) (cube : |p| ≤ D) (direction : |d| ≤ bound)
    (speedBound : 0 ≤ speed ∧ speed ≤ bound) (distanceBound : 0 ≤ distance ∧ distance ≤ 2 * D) :
    |D * speed| ≤ D * bound ∧ |p * speed| ≤ D * bound ∧
      |distance * d| ≤ 2 * D * bound ∧
      |p * speed + distance * d| ≤ 3 * D * bound ∧
      |distance * speed| ≤ 2 * D * bound := by
  have nonnegative : 0 ≤ bound := speedBound.1.trans speedBound.2
  have ds : |D * speed| ≤ D * bound := by
    rw [abs_of_nonneg (mul_nonneg positive speedBound.1)]
    exact mul_le_mul_of_nonneg_left speedBound.2 positive
  have ps : |p * speed| ≤ D * bound := by
    rw [abs_mul, abs_of_nonneg speedBound.1]
    exact mul_le_mul cube speedBound.2 speedBound.1 positive
  have gd : |distance * d| ≤ 2 * D * bound := by
    rw [abs_mul, abs_of_nonneg distanceBound.1]
    exact mul_le_mul distanceBound.2 direction (abs_nonneg _) (by positivity)
  have gs : |distance * speed| ≤ 2 * D * bound := by
    rw [abs_mul, abs_of_nonneg distanceBound.1, abs_of_nonneg speedBound.1]
    exact mul_le_mul distanceBound.2 speedBound.2 speedBound.1 (by positivity)
  refine ⟨ds, ps, gd, ?_, gs⟩
  calc
    |p * speed + distance * d| ≤ |p * speed| + |distance * d| := abs_add_le _ _
    _ ≤ D * bound + 2 * D * bound := add_le_add ps gd
    _ = 3 * D * bound := by ring

theorem signed_fits (bits : ℕ) (x limit : ℤ)
    (magnitude : |x| ≤ limit) (capacity : limit < 2 ^ bits) :
    -(2 ^ bits) ≤ x ∧ x < 2 ^ bits := by
  have bounds := abs_le.mp magnitude
  constructor <;> omega

theorem update_fits (bits : ℕ) (D p d speed distance bound : ℤ)
    (positive : 0 ≤ D) (cube : |p| ≤ D) (direction : |d| ≤ bound)
    (speedBound : 0 ≤ speed ∧ speed ≤ bound) (distanceBound : 0 ≤ distance ∧ distance ≤ 2 * D)
    (capacity : 3 * D * bound < 2 ^ bits) :
    let fits := fun x : ℤ => -(2 ^ bits) ≤ x ∧ x < 2 ^ bits
    fits (D * speed) ∧ fits (p * speed) ∧ fits (distance * d) ∧
      fits (p * speed + distance * d) ∧ fits (distance * speed) := by
  have nonnegative : 0 ≤ bound := speedBound.1.trans speedBound.2
  have product : 0 ≤ D * bound := mul_nonneg positive nonnegative
  obtain ⟨ds, ps, gd, total, gs⟩ := update_bounds D p d speed distance bound positive cube direction speedBound distanceBound
  exact ⟨signed_fits bits _ _ ds (by nlinarith), signed_fits bits _ _ ps (by nlinarith),
    signed_fits bits _ _ gd (by nlinarith), signed_fits bits _ _ total capacity,
    signed_fits bits _ _ gs (by nlinarith)⟩

end Project.Beck.Bounds
