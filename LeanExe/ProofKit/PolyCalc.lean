import LeanExe.ProofKit.AsinRemainder
import LeanExe.ProofKit.PolyCalculus

/-!
Exact rational evaluation of `PolyBound` polynomials, for proofs whose constants and residuals the
kernel computes.  `evalQ p x` is the value over `ℚ`, equal to `eval p x` after the cast, and
`PolyCalculus.derivP` gives the coefficients of the derivative.  `pow1 k` is `(1 + X) ^ k` and
`mono k` is `X ^ k`.
-/

namespace LeanExe.ProofKit.PolyCalc

open PolyBound PolyChecks

/-- The value of `p` at a rational point, over `ℚ`. -/
def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

theorem evalQ_cast (p : List ℚ) (x : ℚ) : ((evalQ p x : ℚ) : ℝ) = eval p x := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih => simp [evalQ, ih]

/-- `(1 + X) ^ k`. -/
def pow1 : ℕ → List ℚ
  | 0 => [1]
  | k + 1 => mulP [1, 1] (pow1 k)

theorem eval_pow1 (k : ℕ) (x : ℝ) : eval (pow1 k) x = (1 + x) ^ k := by
  induction k with
  | zero => simp [pow1]
  | succ k ih => rw [pow1, eval_mulP, ih]; simp; ring

/-- `X ^ k`. -/
def mono (k : ℕ) : List ℚ := List.replicate k 0 ++ [1]

theorem eval_mono (k : ℕ) (x : ℝ) : eval (mono k) x = x ^ k := by
  induction k with
  | zero => simp [mono]
  | succ k ih =>
    simp only [mono, List.replicate_succ, List.cons_append, eval_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

#print axioms evalQ_cast

end LeanExe.ProofKit.PolyCalc
