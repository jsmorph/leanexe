import Mathlib.Tactic
import Mathlib.Analysis.Real.Sqrt

namespace Project.ProofKit.RealSqrtError

theorem relative_error (rounded exactValue delta : ℝ) (hr : 0 ≤ rounded)
    (he : 0 < exactValue) (herr : |rounded - exactValue| ≤ delta * exactValue) :
    |Real.sqrt rounded - Real.sqrt exactValue| ≤ delta * Real.sqrt exactValue := by
  have hrPos := Real.sqrt_nonneg rounded
  have hePos := Real.sqrt_pos.mpr he
  have hrSq := Real.sq_sqrt hr
  have heSq := Real.sq_sqrt he.le
  have hproduct : |Real.sqrt rounded - Real.sqrt exactValue| *
      (Real.sqrt rounded + Real.sqrt exactValue) = |rounded - exactValue| := by
    rw [← abs_of_nonneg (add_nonneg hrPos hePos.le), ← abs_mul]
    congr 1
    nlinarith only [hrSq, heSq]
  have hbound := mul_nonneg (abs_nonneg (Real.sqrt rounded - Real.sqrt exactValue)) hrPos
  have hscaled : |Real.sqrt rounded - Real.sqrt exactValue| * Real.sqrt exactValue ≤
      delta * exactValue := by nlinarith only [herr, hproduct, hbound]
  apply (mul_le_mul_iff_of_pos_right hePos).mp
  calc
    |Real.sqrt rounded - Real.sqrt exactValue| * Real.sqrt exactValue ≤ delta * exactValue := hscaled
    _ = (delta * Real.sqrt exactValue) * Real.sqrt exactValue := by rw [mul_assoc, ← pow_two, heSq]

#print axioms relative_error
end Project.ProofKit.RealSqrtError
