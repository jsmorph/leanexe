import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Project.ProofKit.RealProductError

theorem product_perturbation (a b a' b' bound error : ℝ)
    (ha : |a| ≤ bound) (hb : |b| ≤ bound)
    (hea : |a' - a| ≤ error) (heb : |b' - b| ≤ error) :
    |a' * b' - a * b| ≤ 2 * bound * error + error^2 := by
  have hBound : 0 ≤ bound := (abs_nonneg a).trans ha
  have hError : 0 ≤ error := (abs_nonneg (a' - a)).trans hea
  calc
    |a' * b' - a * b| =
        |a * (b' - b) + b * (a' - a) + (a' - a) * (b' - b)| := by
      congr 1
      ring
    _ ≤ |a * (b' - b)| + |b * (a' - a)| + |(a' - a) * (b' - b)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ bound * error + bound * error + error * error := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul ha heb (abs_nonneg _) hBound)
        (mul_le_mul hb hea (abs_nonneg _) hBound))
        (mul_le_mul hea heb (abs_nonneg _) hError)
    _ = 2 * bound * error + error^2 := by ring

#print axioms product_perturbation
end Project.ProofKit.RealProductError
