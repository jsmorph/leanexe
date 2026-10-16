import LeanExe.ProofKit.PolyChecks
import LeanExe.ProofKit.TaylorRemainder

/-!
Operations on coefficient lists for `PolyBound` beyond sums and products: the formal derivative,
with `HasDerivAt` for `eval`, powers, the substitution `x ↦ x²` (`spread`), odd polynomials
(`oddP`), reversal, and `hatP c n`, whose value at `x ≠ 0` is `x ^ (2 n) eval c (1/x²)`.  With these,
a rational function of `1/x²` and its derivative become quotients of polynomials in `x`, and a
polynomial bound on the numerator of their difference from another function can be checked.
-/

namespace LeanExe.ProofKit.PolyCalculus
open PolyBound PolyChecks TaylorRemainder

/-- The formal derivative. -/
def derivP : List ℚ → List ℚ
  | [] => []
  | _ :: p => addP p (0 :: derivP p)

theorem hasDerivAt_eval (p : List ℚ) (x : ℝ) : HasDerivAt (eval p) (eval (derivP p) x) x := by
  induction p with
  | nil =>
    have h : eval [] = fun _ => (0 : ℝ) := by funext y; rfl
    rw [h]
    exact hasDerivAt_const x 0
  | cons a p ih =>
    have h : eval (a :: p) = fun y => (a : ℝ) + y * eval p y := by funext y; rfl
    rw [h]
    have hd := (hasDerivAt_id x).mul ih
    refine (hd.const_add (a : ℝ)).congr_deriv ?_
    simp only [derivP, eval_addP, eval_cons, Rat.cast_zero, id]
    ring

theorem continuous_eval (p : List ℚ) : Continuous (eval p) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_eval p x).continuousAt

theorem hasDerivAt_eval_sub (p : List ℚ) (c x : ℝ) :
    HasDerivAt (fun y => eval p (y - c)) (eval (derivP p) (x - c)) x := by
  have h := (hasDerivAt_eval p (x - c)).comp x ((hasDerivAt_id x).sub_const c)
  exact h.congr_deriv (by simp)

/-- The `n`-th power. -/
def powP (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => mulP (powP p n) p

theorem eval_powP (p : List ℚ) (n : ℕ) (x : ℝ) : eval (powP p n) x = eval p x ^ n := by
  induction n with
  | zero => simp [powP]
  | succ n ih => rw [powP, eval_mulP, ih, pow_succ]

/-- The coefficients of `p (x²)`. -/
def spread : List ℚ → List ℚ
  | [] => []
  | a :: p => a :: 0 :: spread p

theorem eval_spread (p : List ℚ) (x : ℝ) : eval (spread p) x = eval p (x ^ 2) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [spread, eval_cons, ih, Rat.cast_zero]
    ring

/-- The coefficients of `x p (x²)`. -/
def oddP (p : List ℚ) : List ℚ := 0 :: spread p

theorem eval_oddP (p : List ℚ) (x : ℝ) : eval (oddP p) x = x * eval p (x ^ 2) := by
  simp only [oddP, eval_cons, eval_spread, Rat.cast_zero, zero_add]

theorem eval_replicate_append (k : ℕ) (q : List ℚ) (x : ℝ) :
    eval (List.replicate k 0 ++ q) x = x ^ k * eval q x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, eval_cons, ih]
    simp only [Rat.cast_zero, zero_add]
    ring

theorem eval_reverse (p : List ℚ) (y : ℝ) (hy : y ≠ 0) :
    eval p.reverse y * y = y ^ p.length * eval p y⁻¹ := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [List.reverse_cons, eval_append, List.length_reverse, List.length_cons]
    simp only [eval_cons, eval_nil, mul_zero, add_zero]
    have hyi : y * y⁻¹ = 1 := mul_inv_cancel₀ hy
    calc (eval p.reverse y + y ^ p.length * (a : ℝ)) * y
        = eval p.reverse y * y + y ^ (p.length + 1) * a := by ring
      _ = y ^ p.length * eval p y⁻¹ + y ^ (p.length + 1) * a := by rw [ih]
      _ = y ^ (p.length + 1) * ((a : ℝ) + y⁻¹ * eval p y⁻¹) := by
          rw [pow_succ]
          linear_combination (-(y ^ p.length * eval p y⁻¹)) * hyi

/-- The coefficients of `x ^ (2 n) c (1/x²)`, for `c` of length at most `n + 1`. -/
def hatP (c : List ℚ) (n : ℕ) : List ℚ :=
  spread (List.replicate (n + 1 - c.length) 0 ++ c.reverse)

theorem eval_hatP (c : List ℚ) (n : ℕ) (hc : c.length ≤ n + 1) (x : ℝ) (hx : x ≠ 0) :
    eval (hatP c n) x = x ^ (2 * n) * eval c (x ^ 2)⁻¹ := by
  have hy : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  rw [hatP, eval_spread, eval_replicate_append]
  have hr := eval_reverse c (x ^ 2) hy
  have he : eval c.reverse (x ^ 2) = (x ^ 2) ^ c.length * eval c (x ^ 2)⁻¹ / x ^ 2 := by
    rw [← hr]
    field_simp
  rw [he]
  rcases Nat.eq_zero_or_pos c.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0]
    simp
  · have hk : n + 1 - c.length + c.length = n + 1 := by omega
    have hpow : (x ^ 2) ^ (n + 1 - c.length) * ((x ^ 2) ^ c.length / x ^ 2) = x ^ (2 * n) := by
      rw [mul_div_assoc', ← pow_add, hk, pow_succ, mul_div_assoc, div_self hy, mul_one,
        ← pow_mul]
    calc (x ^ 2) ^ (n + 1 - c.length) * ((x ^ 2) ^ c.length * eval c (x ^ 2)⁻¹ / x ^ 2)
        = ((x ^ 2) ^ (n + 1 - c.length) * ((x ^ 2) ^ c.length / x ^ 2)) *
            eval c (x ^ 2)⁻¹ := by ring
      _ = x ^ (2 * n) * eval c (x ^ 2)⁻¹ := by rw [hpow]

#print axioms hasDerivAt_eval
#print axioms continuous_eval
#print axioms eval_powP
#print axioms eval_spread
#print axioms eval_oddP
#print axioms eval_reverse
#print axioms eval_hatP

end LeanExe.ProofKit.PolyCalculus
