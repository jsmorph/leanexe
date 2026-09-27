import Mathlib.Tactic

namespace Project.Beck.RoundBounds

theorem inside (denominator coordinate direction distance speed : ℤ)
    (cube : |coordinate| ≤ denominator) (forward : 0 ≤ distance) (positive : 0 < speed)
    (limit : direction ≠ 0 → distance * |direction| ≤
      (if direction < 0 then denominator + coordinate else denominator - coordinate) * speed) :
    |coordinate * speed + distance * direction| ≤ denominator * speed := by
  obtain ⟨lower, upper⟩ := abs_le.mp cube
  have lowerScaled := mul_le_mul_of_nonneg_right lower (le_of_lt positive)
  have upperScaled := mul_le_mul_of_nonneg_right upper (le_of_lt positive)
  apply abs_le.mpr
  rcases lt_trichotomy direction 0 with negative | zero | forwardDirection
  · have bound := limit (ne_of_lt negative)
    rw [abs_of_neg negative, ite_eq_left negative] at bound
    have movement := mul_nonpos_of_nonneg_of_nonpos forward (le_of_lt negative)
    constructor <;> nlinarith
  · subst direction
    constructor <;> nlinarith
  · have bound := limit (ne_of_gt forwardDirection)
    rw [abs_of_pos forwardDirection, ite_eq_right (not_lt_of_gt forwardDirection)] at bound
    have movement := mul_nonneg forward (le_of_lt forwardDirection)
    constructor <;> nlinarith

theorem boundary (denominator coordinate direction : ℤ)
    (positive : 0 < denominator) (moving : direction ≠ 0) :
    |coordinate * |direction| +
      (if direction < 0 then denominator + coordinate else denominator - coordinate) * direction| =
        denominator * |direction| := by
  by_cases negative : direction < 0
  · rw [abs_of_neg negative, ite_eq_left negative]
    have equal : coordinate * -direction + (denominator + coordinate) * direction = denominator * direction := by ring
    rw [equal, abs_of_neg (mul_neg_of_pos_of_neg positive negative)]
    ring
  · have forward : 0 < direction := lt_of_le_of_ne (le_of_not_gt negative) (Ne.symm moving)
    rw [abs_of_pos forward, ite_eq_right negative]
    have equal : coordinate * direction + (denominator - coordinate) * direction = denominator * direction := by ring
    rw [equal, abs_of_pos (mul_pos positive forward)]

theorem coordinate (denominator numerator direction distance speed : ℤ)
    (denominatorNonzero : denominator ≠ 0) (speedNonzero : speed ≠ 0) :
    ((numerator * speed + distance * direction : ℤ) : ℚ) / ((denominator * speed : ℤ) : ℚ) =
      (numerator : ℚ) / (denominator : ℚ) +
        ((distance : ℚ) / ((denominator * speed : ℤ) : ℚ)) * (direction : ℚ) := by
  have denominatorRat : (denominator : ℚ) ≠ 0 := by exact_mod_cast denominatorNonzero
  have speedRat : (speed : ℚ) ≠ 0 := by exact_mod_cast speedNonzero
  push_cast
  field_simp

#print axioms inside
#print axioms boundary

end Project.Beck.RoundBounds
