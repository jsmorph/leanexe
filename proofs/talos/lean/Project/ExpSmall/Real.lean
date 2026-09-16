import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Project.ExpSmall

noncomputable def polynomialReal (x : ℝ) : ℝ :=
  (((((1 / 720 * x + 1 / 120) * x + 1 / 24) * x + 1 / 6) * x + 1 / 2) * x + 1) * x + 1

theorem polynomialReal_error (x : ℝ) (hx : |x| ≤ 1) :
    |polynomialReal x - Real.exp x| ≤ 1 / 4410 := by
  have h := Real.exp_bound hx (n := 7) (by norm_num)
  have hs : (∑ m ∈ Finset.range 7, x ^ m / (m.factorial : ℝ)) = polynomialReal x := by
    norm_num [Finset.sum_range_succ, polynomialReal]
    ring
  rw [hs] at h
  have hp : |x| ^ 7 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  rw [abs_sub_comm]
  apply h.trans
  norm_num [Nat.factorial] at *
  linarith

#print axioms polynomialReal_error
end Project.ExpSmall
