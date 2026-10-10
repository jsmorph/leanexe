import LeanExe.ProofKit.TaylorRemainder

/-!
The series `log (1 + x) - log (1 - x) = Σ 2 x ^ (2 k + 1) / (2 k + 1)` truncated as a polynomial in
`z = x ^ 2`, with the remainder bound for `|x| < 1` from `Real.hasSum_log_sub_log_of_abs_lt_one` and
the geometric majorant `2 |x| ^ (2 n + 1) (x ^ 2) ^ k`.  fdlibm's `log1p` and `log` write
`log (1 + f)` as `log (1 + s) - log (1 - s)` with `s = f/(2 + f)`.
-/

namespace LeanExe.ProofKit.LogRatioRemainder
open PolyBound TaylorRemainder Finset

/-- `Σ k < n, 2 z ^ k / (2 k + 1)`. -/
def logRatioCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => 2 / ((2 * k + 1 : ℕ) : ℚ)

theorem log_ratio_remainder (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    |Real.log (1 + x) - Real.log (1 - x) - x * eval (logRatioCoeffs n) (x ^ 2)| ≤
      2 * |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  let f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1)
  have hs : HasSum f (Real.log (1 + x) - Real.log (1 - x)) :=
    Real.hasSum_log_sub_log_of_abs_lt_one hx
  have htail := (hasSum_nat_add_iff' (f := f) n).mpr hs
  have hpoly : x * eval (logRatioCoeffs n) (x ^ 2) = ∑ i ∈ range n, f i := by
    rw [logRatioCoeffs, eval_map_range, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [f]
    push_cast
    ring
  have hx2 : x ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg x) hx2).mul_left (2 * |x| ^ (2 * n + 1))
  have hb : ∀ k : ℕ, ‖f (k + n)‖ ≤ 2 * |x| ^ (2 * n + 1) * (x ^ 2) ^ k := by
    intro k
    have hd : (1 : ℝ) ≤ 2 * ((k + n : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((k + n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    simp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * ((k + n : ℕ) : ℝ) + 1))]
    have he : 2 * |x| ^ (2 * n + 1) * (x ^ 2) ^ k = 2 * |x| ^ (2 * (k + n) + 1) := by
      rw [← sq_abs x, ← pow_mul, mul_assoc, ← pow_add]
      ring_nf
    rw [he]
    have hq : 1 / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hd
    have hp : 0 ≤ |x| ^ (2 * (k + n) + 1) := by positivity
    calc 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * |x| ^ (2 * (k + n) + 1) ≤
        2 * 1 * |x| ^ (2 * (k + n) + 1) := by gcongr
      _ = 2 * |x| ^ (2 * (k + n) + 1) := by ring
  have h := htail.norm_le_of_bounded hg hb
  rw [Real.norm_eq_abs] at h
  rw [show Real.log (1 + x) - Real.log (1 - x) - x * eval (logRatioCoeffs n) (x ^ 2) =
    Real.log (1 + x) - Real.log (1 - x) - ∑ i ∈ range n, f i by rw [hpoly], div_eq_mul_inv]
  exact h

#print axioms log_ratio_remainder

end LeanExe.ProofKit.LogRatioRemainder
