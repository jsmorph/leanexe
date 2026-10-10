import LeanExe.ProofKit.TaylorRemainder
import LeanExe.ProofKit.PolyChecks
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
A Taylor remainder for `arcsin` on `|x| ≤ 1/2`, which Mathlib lacks.  The derivative of
`arcsin` is `(1 - t ^ 2) ^ (-1/2)`, whose series in `u = t ^ 2` has the coefficients
`binCoeff k = (2k choose k) / 4 ^ k`.  For the truncation `S` to `n` terms,
`1 - (1 - u) S(u) ^ 2` is a polynomial `invSqrtDefect n` with no terms below degree `n`, a fact
that the kernel checks for a given `n`, so that `1 - (1 - u) S(u) ^ 2 = u ^ n G(u)`.  With
`y = 1/√(1 - u)`, `(y - S) (1 - u) (y + S) = u ^ n G(u)`, and `y ≥ 1`, `S ≥ 0`, and `u ≤ 1/4`
give `|y - S| ≤ (4/3) γ u ^ n` when `|G| ≤ γ` on `[0, 1/4]`.  The mean value inequality then
bounds `arcsin x - Σ k < n, binCoeff k x ^ (2k + 1) / (2k + 1)` by `(4/3) γ |x| ^ (2n + 1)`.
-/

namespace LeanExe.ProofKit.AsinRemainder
open PolyBound PolyChecks TaylorRemainder Finset

/-- `(2k choose k) / 4 ^ k`, the coefficient of `u ^ k` in `(1 - u) ^ (-1/2)`. -/
def binCoeff (k : ℕ) : ℚ := ((2 * k).choose k : ℚ) / 4 ^ k

/-- `Σ k < n, binCoeff k u ^ k`. -/
def invSqrtCoeffs (n : ℕ) : List ℚ := (List.range n).map binCoeff

/-- `Σ k < n, binCoeff k z ^ k / (2k + 1)`: `x * eval (asinCoeffs n) (x ^ 2)` is the Taylor
polynomial of `arcsin x`. -/
def asinCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => binCoeff k / ((2 * k + 1 : ℕ) : ℚ)

/-- `1 - (1 - u) S(u) ^ 2` for `S = eval (invSqrtCoeffs n)`. -/
def invSqrtDefect (n : ℕ) : List ℚ :=
  subP [1] (mulP [1, -1] (mulP (invSqrtCoeffs n) (invSqrtCoeffs n)))

theorem eval_take_drop (p : List ℚ) (n : ℕ) (x : ℝ) :
    eval p x = eval (p.take n) x + x ^ n * eval (p.drop n) x := by
  conv_lhs => rw [← List.take_append_drop n p]
  rw [eval_append]
  by_cases h : n ≤ p.length
  · rw [List.length_take, min_eq_left h]
  · have hd : p.drop n = [] := List.drop_eq_nil_of_le (by omega)
    simp [hd]

theorem eval_eq_zero_of_all (p : List ℚ) (h : p.all (fun a => decide (a = 0)) = true) (x : ℝ) :
    eval p x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [eval_cons, h.1, ih h.2, Rat.cast_zero, mul_zero, add_zero]

theorem eval_nonneg (p : List ℚ) (h : ∀ a ∈ p, 0 ≤ a) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ eval p x := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [eval_cons]
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h a (List.mem_cons_self ..)
    have hp := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    positivity

theorem binCoeff_nonneg (k : ℕ) : 0 ≤ binCoeff k := by
  unfold binCoeff
  positivity

theorem eval_invSqrtDefect (n : ℕ) (u : ℝ) :
    eval (invSqrtDefect n) u = 1 - (1 - u) * eval (invSqrtCoeffs n) u ^ 2 := by
  simp only [invSqrtDefect, eval_subP, eval_mulP, eval_cons, eval_nil, Rat.cast_one,
    Rat.cast_neg]
  ring

/-- The truncated binomial series of `(1 - u) ^ (-1/2)` on `[0, 1/4]`. -/
theorem inv_sqrt_error (n : ℕ) (γ : ℚ)
    (hz : ((invSqrtDefect n).take n).all (fun a => decide (a = 0)) = true)
    (hγ : Bounded ((invSqrtDefect n).drop n) 0 (1 / 4) γ) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 4) :
    |1 / √(1 - u) - eval (invSqrtCoeffs n) u| ≤ 4 / 3 * γ * u ^ n := by
  set S := eval (invSqrtCoeffs n) u with hS
  set y := 1 / √(1 - u) with hy
  have hS0 : 0 ≤ S := eval_nonneg _ (fun a ha => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
    exact binCoeff_nonneg k) u hu0
  have h1u : (3 / 4 : ℝ) ≤ 1 - u := by linarith
  have hsq : 0 < √(1 - u) := Real.sqrt_pos.mpr (by linarith)
  have hsq1 : √(1 - u) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ hsq, one_mul]
    exact hsq1
  have hyy : (1 - u) * y ^ 2 = 1 := by
    rw [hy, div_pow, Real.sq_sqrt (by linarith)]
    field_simp
  have hid : (y - S) * ((1 - u) * (y + S)) = 1 - (1 - u) * S ^ 2 := by
    linear_combination hyy
  have hG : |eval ((invSqrtDefect n).drop n) u| ≤ γ :=
    hγ u (by simpa using hu0) (by push_cast; linarith)
  have hdef : 1 - (1 - u) * S ^ 2 = u ^ n * eval ((invSqrtDefect n).drop n) u := by
    rw [← eval_invSqrtDefect, eval_take_drop _ n, eval_eq_zero_of_all _ hz, zero_add]
  have hpos : 0 < (1 - u) * (y + S) := by positivity
  have habs : |y - S| * ((1 - u) * (y + S)) ≤ u ^ n * γ := by
    rw [← abs_of_pos hpos, ← abs_mul, hid, hdef, abs_mul, abs_of_nonneg (pow_nonneg hu0 n)]
    exact mul_le_mul_of_nonneg_left hG (pow_nonneg hu0 n)
  have hden : (3 / 4 : ℝ) ≤ (1 - u) * (y + S) := by nlinarith
  have h34 : |y - S| * (3 / 4) ≤ u ^ n * γ :=
    le_trans (mul_le_mul_of_nonneg_left hden (abs_nonneg _)) habs
  linarith

theorem eval_asinCoeffs (n : ℕ) (x : ℝ) :
    x * eval (asinCoeffs n) (x ^ 2) =
      ∑ k ∈ range n, ((binCoeff k / ((2 * k + 1 : ℕ) : ℚ) : ℚ) : ℝ) * x ^ (2 * k + 1) := by
  rw [asinCoeffs, eval_map_range, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← pow_mul, pow_succ]
  ring

theorem eval_invSqrtCoeffs (n : ℕ) (t : ℝ) :
    eval (invSqrtCoeffs n) (t ^ 2) = ∑ k ∈ range n, (binCoeff k : ℝ) * t ^ (2 * k) := by
  rw [invSqrtCoeffs, eval_map_range]
  refine sum_congr rfl fun k _ => ?_
  rw [← pow_mul]

/-- The Taylor remainder of `arcsin` on `|x| ≤ 1/2`, given the kernel's checks of
`invSqrtDefect n`. -/
theorem asin_remainder (n : ℕ) (γ : ℚ)
    (hz : ((invSqrtDefect n).take n).all (fun a => decide (a = 0)) = true)
    (hγ : Bounded ((invSqrtDefect n).drop n) 0 (1 / 4) γ) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |Real.arcsin x - x * eval (asinCoeffs n) (x ^ 2)| ≤ 4 / 3 * γ * |x| ^ (2 * n + 1) := by
  set a := |x| with ha
  have hγ0 : (0 : ℝ) ≤ γ := by
    have h := hγ 0 (by simp) (by norm_num)
    exact (abs_nonneg _).trans h
  let c : ℕ → ℝ := fun k => ((binCoeff k / ((2 * k + 1 : ℕ) : ℚ) : ℚ) : ℝ)
  let f : ℝ → ℝ := fun t => Real.arcsin t - ∑ k ∈ range n, c k * t ^ (2 * k + 1)
  let f' : ℝ → ℝ := fun t => 1 / √(1 - t ^ 2) - ∑ k ∈ range n, (binCoeff k : ℝ) * t ^ (2 * k)
  have hderiv : ∀ t ∈ Set.Icc (-a) a, HasDerivWithinAt f (f' t) (Set.Icc (-a) a) t := by
    intro t ht
    have hta : |t| ≤ a := abs_le.mpr ⟨ht.1, ht.2⟩
    have ht1 : |t| < 1 := by linarith
    have hn1 : t ≠ -1 := by
      intro h
      rw [h] at ht1
      norm_num at ht1
    have hp1 : t ≠ 1 := by
      intro h
      rw [h] at ht1
      norm_num at ht1
    have hsum : HasDerivAt (fun y => ∑ k ∈ range n, c k * y ^ (2 * k + 1))
        (∑ k ∈ range n, (binCoeff k : ℝ) * t ^ (2 * k)) t := by
      have h0 := HasDerivAt.sum (u := range n) (A := fun k y => c k * y ^ (2 * k + 1))
        (A' := fun k => c k * (((2 * k + 1 : ℕ) : ℝ) * t ^ (2 * k + 1 - 1)))
        (fun k _ => (hasDerivAt_pow (2 * k + 1) t).const_mul (c k))
      have hf : (∑ i ∈ range n, fun y => c i * y ^ (2 * i + 1)) =
          fun y => ∑ k ∈ range n, c k * y ^ (2 * k + 1) := by
        funext y
        rw [Finset.sum_apply]
      rw [hf] at h0
      refine h0.congr_deriv (sum_congr rfl fun k _ => ?_)
      simp only [c, Nat.add_sub_cancel]
      have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    exact ((Real.hasDerivAt_arcsin hn1 hp1).sub hsum).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (-a) a, ‖f' t‖ ≤ 4 / 3 * γ * a ^ (2 * n) := by
    intro t ht
    have hta : |t| ≤ a := abs_le.mpr ⟨ht.1, ht.2⟩
    have hu1 : t ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg t]
    have he := inv_sqrt_error n γ hz hγ (t ^ 2) (sq_nonneg t) hu1
    rw [eval_invSqrtCoeffs] at he
    rw [Real.norm_eq_abs]
    have hpow : (t ^ 2) ^ n ≤ a ^ (2 * n) := by
      rw [← sq_abs t, ← pow_mul]
      exact pow_le_pow_left₀ (abs_nonneg t) hta _
    calc |f' t| ≤ 4 / 3 * γ * (t ^ 2) ^ n := he
      _ ≤ 4 / 3 * γ * a ^ (2 * n) := by gcongr
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc _ _)
    (show (0 : ℝ) ∈ Set.Icc (-a) a from ⟨by simp [ha], by simp [ha]⟩)
    (show x ∈ Set.Icc (-a) a from ⟨neg_abs_le x, le_abs_self x⟩)
  have hf0 : f 0 = 0 := by
    simp only [f, Real.arcsin_zero, zero_sub, neg_eq_zero]
    exact sum_eq_zero fun k _ => by rw [zero_pow (by omega), mul_zero]
  rw [hf0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hfx : f x = Real.arcsin x - x * eval (asinCoeffs n) (x ^ 2) := by
    simp only [f, c, eval_asinCoeffs]
  rw [hfx] at hmvt
  calc |Real.arcsin x - x * eval (asinCoeffs n) (x ^ 2)| ≤ 4 / 3 * γ * a ^ (2 * n) * a := hmvt
    _ = 4 / 3 * γ * |x| ^ (2 * n + 1) := by rw [pow_succ]; ring

#print axioms eval_take_drop
#print axioms inv_sqrt_error
#print axioms asin_remainder

end LeanExe.ProofKit.AsinRemainder
