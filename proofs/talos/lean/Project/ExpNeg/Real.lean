import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Project.ExpNeg

noncomputable def polynomialReal (x : ℝ) : ℝ :=
  ((((((((((((((((((1 / 6402373705728000 * x + 1 / 355687428096000) * x + 1 / 20922789888000) * x + 1 / 1307674368000) * x + 1 / 87178291200) * x + 1 / 6227020800) * x + 1 / 479001600) * x + 1 / 39916800) * x + 1 / 3628800) * x + 1 / 362880) * x + 1 / 40320) * x + 1 / 5040) * x + 1 / 720) * x + 1 / 120) * x + 1 / 24) * x + 1 / 6) * x + 1 / 2) * x + 1 / 1) * x + 1 / 1)

theorem polynomialReal_error (x : ℝ) (hx : |x| ≤ 1) :
    |polynomialReal x - Real.exp x| ≤ 1 / 100000000000000000 := by
  have h := Real.exp_bound hx (n := 19) (by norm_num)
  have hs : (∑ m ∈ Finset.range 19, x ^ m / (m.factorial : ℝ)) = polynomialReal x := by
    norm_num [Finset.sum_range_succ, polynomialReal]
    ring
  rw [hs] at h
  have hp : |x| ^ 19 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  rw [abs_sub_comm]
  apply h.trans
  norm_num [Nat.factorial] at *
  linarith

#print axioms polynomialReal_error
end Project.ExpNeg
