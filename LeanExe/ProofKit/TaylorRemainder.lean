import LeanExe.ProofKit.PolyBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Taylor polynomials as coefficient lists for `PolyBound`, and bounds on their remainders.  The
sine, cosine, and arctangent polynomials are in `z = x ^ 2`: `sin x` is approximated by
`x * eval (sinCoeffs n) (x ^ 2)`, `cos x` by `eval (cosCoeffs n) (x ^ 2)`, and `arctan x` by
`x * eval (atanCoeffs n) (x ^ 2)`.  The exponential and `log (1 + x)` polynomials are in `x`.
The sine and cosine bounds hold for `|x| ≤ 1`, from the series of `Real.sin` and `Real.cos`
with a geometric majorant of ratio `1/2`.  The arctangent bound holds for `|x| < 1`, from
`Real.hasSum_arctan`, the exponential bound from `Real.exp_bound`, and the logarithm bound from
`Real.abs_log_sub_add_sum_range_le`.
-/

namespace LeanExe.ProofKit.TaylorRemainder
open PolyBound Finset

/-- `Σ k < n, (-1) ^ k z ^ k / (2 k + 1)!`. -/
def sinCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => (-1) ^ k / ((2 * k + 1).factorial : ℚ)

/-- `Σ k < n, (-1) ^ k z ^ k / (2 k)!`. -/
def cosCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => (-1) ^ k / ((2 * k).factorial : ℚ)

/-- `Σ k < n, x ^ k / k!`. -/
def expCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => 1 / (k.factorial : ℚ)

/-- `Σ k < n, (-1) ^ k x ^ k / (k + 1)`, the Taylor polynomial of `log (1 + x) / x`. -/
def log1pQuotCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => (-1) ^ k / ((k + 1 : ℕ) : ℚ)

/-- `Σ k < n, (-1) ^ k x ^ (k + 1) / (k + 1)`. -/
def log1pCoeffs (n : ℕ) : List ℚ := 0 :: log1pQuotCoeffs n

/-- `Σ k < n, (-1) ^ k z ^ k / (2 k + 1)`. -/
def atanCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => (-1) ^ k / ((2 * k + 1 : ℕ) : ℚ)

theorem eval_append (p q : List ℚ) (x : ℝ) :
    eval (p ++ q) x = eval p x + x ^ p.length * eval q x := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.cons_append, eval_cons, ih, List.length_cons, pow_succ]
    ring

theorem eval_map_range (f : ℕ → ℚ) (n : ℕ) (x : ℝ) :
    eval ((List.range n).map f) x = ∑ k ∈ range n, (f k : ℝ) * x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, eval_append, ih, sum_range_succ]
    simp only [List.map_cons, List.map_nil, eval_cons, eval_nil, List.length_map,
      List.length_range, mul_zero, add_zero]
    ring

theorem factorial_add_two (m : ℕ) : 2 * m.factorial ≤ (m + 2).factorial := by
  show 2 * m.factorial ≤ (m + 1 + 1).factorial
  rw [Nat.factorial_succ, Nat.factorial_succ]
  have h : 2 ≤ (m + 1 + 1) * (m + 1) := by nlinarith
  calc 2 * m.factorial ≤ ((m + 1 + 1) * (m + 1)) * m.factorial := Nat.mul_le_mul_right _ h
    _ = (m + 1 + 1) * ((m + 1) * m.factorial) := by ring

theorem factorial_odd_ge (n k : ℕ) :
    (2 * n + 1).factorial * 2 ^ k ≤ (2 * (k + n) + 1).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := factorial_add_two (2 * (k + n) + 1)
    have he : 2 * (k + 1 + n) + 1 = 2 * (k + n) + 1 + 2 := by ring
    rw [he, pow_succ]
    calc (2 * n + 1).factorial * (2 ^ k * 2) = ((2 * n + 1).factorial * 2 ^ k) * 2 := by ring
      _ ≤ (2 * (k + n) + 1).factorial * 2 := by gcongr
      _ ≤ _ := by linarith

theorem factorial_even_ge (n k : ℕ) :
    (2 * n).factorial * 2 ^ k ≤ (2 * (k + n)).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := factorial_add_two (2 * (k + n))
    have he : 2 * (k + 1 + n) = 2 * (k + n) + 2 := by ring
    rw [he, pow_succ]
    calc (2 * n).factorial * (2 ^ k * 2) = ((2 * n).factorial * 2 ^ k) * 2 := by ring
      _ ≤ (2 * (k + n)).factorial * 2 := by gcongr
      _ ≤ _ := by linarith

/-- A term `c x ^ m / D` of a series, bounded by `|x| ^ m₀ / D₀ (1/2) ^ k` when `|x| ≤ 1`,
`m₀ ≤ m`, `|c| = 1`, and `D₀ 2 ^ k ≤ D`. -/
theorem term_le (x c : ℝ) (hc : |c| = 1) (hx : |x| ≤ 1) (m m₀ k : ℕ) (hm : m₀ ≤ m) (D D₀ : ℕ)
    (hD₀ : 0 < D₀) (hD : D₀ * 2 ^ k ≤ D) :
    ‖c * x ^ m / (D : ℝ)‖ ≤ |x| ^ m₀ / D₀ * ((1 : ℝ) / 2) ^ k := by
  have hD₀' : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  have hD' : ((D₀ : ℝ) * 2 ^ k) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD'
  have hxm : |x| ^ m ≤ |x| ^ m₀ := pow_le_pow_of_le_one (abs_nonneg x) hx hm
  rw [Real.norm_eq_abs, abs_div, abs_mul, hc, one_mul, abs_pow, Nat.abs_cast,
    div_le_iff₀ hDpos]
  calc |x| ^ m ≤ |x| ^ m₀ := hxm
    _ = |x| ^ m₀ / D₀ * ((1 : ℝ) / 2) ^ k * ((D₀ : ℝ) * 2 ^ k) := by
        have h2 : ((1 : ℝ) / 2) ^ k * 2 ^ k = 1 := by
          rw [← mul_pow]
          norm_num
        rw [show |x| ^ m₀ / D₀ * ((1 : ℝ) / 2) ^ k * ((D₀ : ℝ) * 2 ^ k) =
          |x| ^ m₀ * ((D₀ : ℝ) / D₀) * (((1 : ℝ) / 2) ^ k * 2 ^ k) by ring,
          div_self hD₀'.ne', h2, mul_one, mul_one]
    _ ≤ |x| ^ m₀ / D₀ * ((1 : ℝ) / 2) ^ k * D := by gcongr

theorem neg_one_pow_abs (k : ℕ) : |(-1 : ℝ) ^ k| = 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

theorem sin_remainder (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |Real.sin x - x * eval (sinCoeffs n) (x ^ 2)| ≤
      2 * |x| ^ (2 * n + 1) / (2 * n + 1).factorial := by
  let f : ℕ → ℝ := fun k => (-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
  have htail := (hasSum_nat_add_iff' (f := f) n).mpr (Real.hasSum_sin x)
  have hpoly : x * eval (sinCoeffs n) (x ^ 2) = ∑ i ∈ range n, f i := by
    rw [sinCoeffs, eval_map_range, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [f]
    push_cast
    ring
  have hg := (hasSum_geometric_two).mul_left (|x| ^ (2 * n + 1) / (2 * n + 1).factorial)
  have hb : ∀ k : ℕ, ‖f (k + n)‖ ≤
      |x| ^ (2 * n + 1) / (2 * n + 1).factorial * ((1 : ℝ) / 2) ^ k := fun k =>
    term_le x _ (neg_one_pow_abs _) hx _ _ k (by omega) _ _ (Nat.factorial_pos _)
      (factorial_odd_ge n k)
  have h := htail.norm_le_of_bounded hg hb
  rw [Real.norm_eq_abs] at h
  rw [hpoly, show 2 * |x| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) =
    |x| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) * 2 by ring]
  exact h

theorem cos_remainder (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |Real.cos x - eval (cosCoeffs n) (x ^ 2)| ≤ 2 * |x| ^ (2 * n) / (2 * n).factorial := by
  let f : ℕ → ℝ := fun k => (-1) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)
  have htail := (hasSum_nat_add_iff' (f := f) n).mpr (Real.hasSum_cos x)
  have hpoly : eval (cosCoeffs n) (x ^ 2) = ∑ i ∈ range n, f i := by
    rw [cosCoeffs, eval_map_range]
    refine sum_congr rfl fun k _ => ?_
    simp only [f]
    push_cast
    ring
  have hg := (hasSum_geometric_two).mul_left (|x| ^ (2 * n) / (2 * n).factorial)
  have hb : ∀ k : ℕ, ‖f (k + n)‖ ≤
      |x| ^ (2 * n) / (2 * n).factorial * ((1 : ℝ) / 2) ^ k := fun k =>
    term_le x _ (neg_one_pow_abs _) hx _ _ k (by omega) _ _ (Nat.factorial_pos _)
      (factorial_even_ge n k)
  have h := htail.norm_le_of_bounded hg hb
  rw [Real.norm_eq_abs] at h
  rw [hpoly, show 2 * |x| ^ (2 * n) / ((2 * n).factorial : ℝ) =
    |x| ^ (2 * n) / ((2 * n).factorial : ℝ) * 2 by ring]
  exact h

theorem exp_remainder (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.exp x - eval (expCoeffs n) x| ≤ |x| ^ n * ((n + 1 : ℝ) / (n.factorial * n)) := by
  have h := Real.exp_bound hx hn
  have hpoly : eval (expCoeffs n) x = ∑ m ∈ range n, x ^ m / m.factorial := by
    rw [expCoeffs, eval_map_range]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hpoly]
  convert h using 2
  push_cast
  ring

theorem eval_log1pCoeffs (n : ℕ) (x : ℝ) :
    eval (log1pCoeffs n) x = x * eval (log1pQuotCoeffs n) x := by
  rw [log1pCoeffs, eval_cons, Rat.cast_zero, zero_add]

theorem log1p_remainder (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    |Real.log (1 + x) - eval (log1pCoeffs n) x| ≤ |x| ^ (n + 1) / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rwa [abs_neg]) n
  rw [abs_neg, sub_neg_eq_add] at h
  have hpoly : eval (log1pCoeffs n) x = -∑ i ∈ range n, (-x) ^ (i + 1) / (i + 1) := by
    rw [log1pCoeffs, log1pQuotCoeffs, eval_cons, eval_map_range, Rat.cast_zero, zero_add, mul_sum,
      ← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hpoly, sub_neg_eq_add, add_comm]
  exact h

theorem atan_remainder (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    |Real.arctan x - x * eval (atanCoeffs n) (x ^ 2)| ≤ |x| ^ (2 * n + 1) / (1 - x ^ 2) := by
  let f : ℕ → ℝ := fun k => (-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)
  have hs : HasSum f (Real.arctan x) := Real.hasSum_arctan (by rwa [Real.norm_eq_abs])
  have htail := (hasSum_nat_add_iff' (f := f) n).mpr hs
  have hpoly : x * eval (atanCoeffs n) (x ^ 2) = ∑ i ∈ range n, f i := by
    rw [atanCoeffs, eval_map_range, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [f]
    push_cast
    ring
  have hx2 : x ^ 2 < 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg x) hx2).mul_left (|x| ^ (2 * n + 1))
  have hb : ∀ k : ℕ, ‖f (k + n)‖ ≤ |x| ^ (2 * n + 1) * (x ^ 2) ^ k := by
    intro k
    have hd : (1 : ℝ) ≤ ((2 * (k + n) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * (k + n) + 1 by omega)
    simp only [f]
    rw [Real.norm_eq_abs, abs_div, abs_mul, neg_one_pow_abs, one_mul, abs_pow, Nat.abs_cast,
      div_le_iff₀ (by linarith)]
    have he : |x| ^ (2 * n + 1) * (x ^ 2) ^ k = |x| ^ (2 * (k + n) + 1) := by
      rw [← sq_abs x, ← pow_mul, ← pow_add]
      ring_nf
    rw [he]
    have hp : 0 ≤ |x| ^ (2 * (k + n) + 1) := by positivity
    nlinarith
  have h := htail.norm_le_of_bounded hg hb
  rw [Real.norm_eq_abs] at h
  rw [hpoly, div_eq_mul_inv]
  linarith

#print axioms eval_map_range
#print axioms sin_remainder
#print axioms cos_remainder
#print axioms exp_remainder
#print axioms eval_log1pCoeffs
#print axioms log1p_remainder
#print axioms atan_remainder

end LeanExe.ProofKit.TaylorRemainder
