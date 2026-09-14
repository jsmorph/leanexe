import Project.ProofKit.RealMinmod
import Mathlib.Algebra.Order.Group.MinMax

namespace Project.ProofKit.RealMinmod

theorem minmod_eq_middle (a b : ℝ) :
    minmod a b = max (min a b) (min (max a b) 0) := by
  simp only [minmod, min_def, max_def]
  split_ifs <;> linarith

theorem minmod_error (a b c d : ℝ) :
    |minmod a b - minmod c d| ≤ max |a-c| |b-d| := by
  rw [minmod_eq_middle, minmod_eq_middle]
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le (abs_min_sub_min_le_max a b c d)
  have h : |min (max a b) 0 - min (max c d) 0| ≤ |max a b - max c d| := by
    simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (max a b - max c d))] using
      abs_min_sub_min_le_max (max a b) 0 (max c d) 0
  exact h.trans (abs_max_sub_max_le_max a b c d)

#print axioms minmod_eq_middle
#print axioms minmod_error

end Project.ProofKit.RealMinmod
