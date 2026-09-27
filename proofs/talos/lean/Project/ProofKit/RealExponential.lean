import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Project.ProofKit.RealExponential

theorem relative_perturbation (x y error : ℝ) (he : |y-x| ≤ error) (hu : error ≤ 1) :
    |Real.exp y-Real.exp x| ≤ 2*error*Real.exp x := by
  have hh := Real.abs_exp_sub_one_le (he.trans hu)
  have hid : Real.exp y-Real.exp x = Real.exp x*(Real.exp (y-x)-1) := by
    rw [mul_sub, ← Real.exp_add, show x+(y-x) = y by ring, mul_one]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos x), mul_comm]
  exact mul_le_mul_of_nonneg_right (hh.trans (by linarith)) (Real.exp_pos x).le

#print axioms relative_perturbation
end Project.ProofKit.RealExponential
