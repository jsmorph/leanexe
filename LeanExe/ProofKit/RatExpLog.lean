import LeanExe.ProofKit.RealExpError
import LeanExe.ProofKit.PolyBound

/-!
Enclosures of `exp` and `log` at rational points, checked by the kernel.  `expSum q n` is the
Taylor sum `Σ k < n, q ^ k / k!` over `ℚ`, and `expRem n = (n + 1)/(n! n)` bounds its error for
`|q| ≤ 1` (`RealExpError.taylor_error_one`).  `le_log` and `log_le` turn a checked comparison of
`expSum q n ± expRem n` with a positive rational `a` into `q ≤ log a` or `log a ≤ q`.  `qeval`
evaluates a `PolyBound` coefficient list over `ℚ`, and `qeval_cast` relates it to
`PolyBound.eval`.
-/

namespace LeanExe.ProofKit.RatExpLog

open Real Finset

/-- `Σ k < n, q ^ k / k!`. -/
def expSum (q : ℚ) (n : ℕ) : ℚ := ∑ k ∈ range n, q ^ k / (k.factorial : ℚ)

/-- `(n + 1)/(n! n)`, the bound on `|exp q - expSum q n|` for `|q| ≤ 1`. -/
def expRem (n : ℕ) : ℚ := (n + 1 : ℚ) / ((n.factorial : ℚ) * n)

theorem abs_exp_sub_le (q : ℚ) (hq : |q| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |exp (q : ℝ) - (expSum q n : ℝ)| ≤ (expRem n : ℝ) := by
  have h := RealExpError.taylor_error_one (q : ℝ) (by exact_mod_cast hq) n hn
  have hs : ((expSum q n : ℚ) : ℝ) = ∑ k ∈ range n, (q : ℝ) ^ k / (k.factorial : ℝ) := by
    simp [expSum]
  have hr : ((expRem n : ℚ) : ℝ) = (n + 1 : ℝ) / (n.factorial * n) := by
    simp [expRem]
  rw [hs, hr]
  exact h

theorem le_log (a q : ℚ) (n : ℕ) (hn : 0 < n) (hq : |q| ≤ 1) (h : expSum q n + expRem n ≤ a) :
    (q : ℝ) ≤ log a := by
  have he := (abs_le.mp (abs_exp_sub_le q hq n hn)).2
  have hr : ((expSum q n + expRem n : ℚ) : ℝ) ≤ a := by exact_mod_cast h
  push_cast at hr
  have ha : (0 : ℝ) < a := by linarith [exp_pos (q : ℝ)]
  rw [le_log_iff_exp_le ha]
  linarith

theorem log_le (a q : ℚ) (n : ℕ) (hn : 0 < n) (hq : |q| ≤ 1) (ha : 0 < a)
    (h : a ≤ expSum q n - expRem n) : log a ≤ (q : ℝ) := by
  have he := (abs_le.mp (abs_exp_sub_le q hq n hn)).1
  have hr : (a : ℝ) ≤ ((expSum q n - expRem n : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  rw [log_le_iff_le_exp (by exact_mod_cast ha)]
  linarith

/-- The value of a coefficient list at a rational point, computed over `ℚ`. -/
def qeval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * qeval p x

theorem qeval_cast (p : List ℚ) (x : ℚ) : ((qeval p x : ℚ) : ℝ) = PolyBound.eval p (x : ℝ) := by
  induction p with
  | nil => simp [qeval]
  | cons a p ih => simp [qeval, ih]

#print axioms abs_exp_sub_le
#print axioms le_log
#print axioms log_le
#print axioms qeval_cast

end LeanExe.ProofKit.RatExpLog
