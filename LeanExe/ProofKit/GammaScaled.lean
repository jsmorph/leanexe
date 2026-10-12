import LeanExe.ProofKit.GammaRel

/-!
Relative bounds on polynomials against `Γ` scaled by a power of two, for the ranges of
CORE-MATH's accurate path, where `Γ` reaches `2 ^ 942`.  `gammaScaledOk c d k l2lo l2hi Q ...`
computes the Taylor model of `exp (lgammaExpr d - k log 2)`, which approximates
`Γ (a + t) / 2 ^ k` with the relative error `2 ρ` of Stirling's remainder (`scaled_model`), and
checks `Q` against it with `GammaRel.relOk`; `gammaScaledOk_sound` gives
`|Γ (a + t)/2 ^ k - Q t| ≤ ε' Γ (a + t)/2 ^ k`.  `dilate c p` has the coefficients of `p (c t)`.
-/

namespace LeanExe.ProofKit.GammaScaled

open Real Finset PolyBound PolyChecks TaylorModel GammaBasic GammaStirling GammaModels GammaRel

/-- The coefficients of `p (c t)`. -/
def dilate (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => a :: scaleP c (dilate c p)

theorem eval_dilate (c : ℚ) (p : List ℚ) (t : ℝ) : eval (dilate c p) t = eval p (c * t) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [dilate, eval_cons, eval_scaleP, ih]
    ring

/-- The model of `Γ (a + t) / 2 ^ k`. -/
def scaledExpr (d : LgData) (k : ℕ) (l2lo l2hi : ℚ) : Expr :=
  .exp (.add (lgammaExpr d) (.mul (.const (-(k : ℚ))) (.logC 2 l2lo l2hi)))

theorem scaled_model (d : LgData) (c : Cfg) (hr : 0 ≤ c.r)
    (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (ha : c.r < d.a) (hY : 16 + c.r ≤ d.a + d.n)
    (hρ : stirRem d c.r ≤ 1) (k : ℕ) (l2lo l2hi : ℚ) {T : TM}
    (hT : tm c (scaledExpr d k l2lo l2hi) = some T) {t : ℝ} (ht : |t| ≤ c.r) :
    |Gamma (d.a + t) / 2 ^ k - eval T.p t| ≤
      T.e + 2 * stirRem d c.r * (((absSum c.r T.p : ℚ) : ℝ) + T.e) := by
  have hrr : (c.r : ℝ) < d.a := by exact_mod_cast ha
  have htr := abs_le.mp ht
  have hpos : 0 < (d.a : ℝ) + t := by linarith
  have h1 := lgamma_sub_expr_le d hr ha hY ht
  have h2 := tm_sound c hr hpi _ hT t ht
  have hM : (scaledExpr d k l2lo l2hi).eval t =
      Real.exp ((lgammaExpr d).eval t - k * Real.log 2) := by
    simp only [scaledExpr, Expr.eval]
    push_cast
    congr 1
    ring
  set E := (lgammaExpr d).eval t
  have hG : Gamma (d.a + t) / 2 ^ k = Real.exp (lgamma (d.a + t) - k * Real.log 2) := by
    rw [Real.exp_sub, lgamma, Real.exp_log (Gamma_pos_of_pos hpos), ← Real.log_pow,
      Real.exp_log (by positivity)]
  rw [hM] at h2
  have hEb : Real.exp (E - k * Real.log 2) ≤ ((absSum c.r T.p : ℚ) : ℝ) + T.e := by
    have h3 := abs_eval_le c.r hr T.p t ht
    have := le_abs_self (Real.exp (E - k * Real.log 2) - eval T.p t)
    have := le_abs_self (eval T.p t)
    linarith
  have hd : |Real.exp (lgamma (d.a + t) - k * Real.log 2) - Real.exp (E - k * Real.log 2)| ≤
      Real.exp (E - k * Real.log 2) * (2 * stirRem d c.r) := by
    have hx : |lgamma (d.a + t) - E| ≤ 1 := h1.trans hρ
    have h5 := Real.abs_exp_sub_one_le hx
    have he : Real.exp (lgamma (d.a + t) - k * Real.log 2) - Real.exp (E - k * Real.log 2) =
        Real.exp (E - k * Real.log 2) * (Real.exp (lgamma (d.a + t) - E) - 1) := by
      rw [mul_sub, ← Real.exp_add, mul_one]
      ring_nf
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (h5.trans (by linarith)) (Real.exp_pos _).le
  rw [hG]
  have hs : 0 ≤ stirRem d c.r := (abs_nonneg _).trans h1
  have := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ 2 * stirRem d c.r)
  calc |Real.exp (lgamma (d.a + t) - k * Real.log 2) - eval T.p t|
      = |(Real.exp (lgamma (d.a + t) - k * Real.log 2) - Real.exp (E - k * Real.log 2)) +
          (Real.exp (E - k * Real.log 2) - eval T.p t)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

/-- The kernel check of `Q` against `Γ (a + t) / 2 ^ k` with relative bound `ε'`. -/
def gammaScaledOk (c : Cfg) (d : LgData) (k : ℕ) (l2lo l2hi : ℚ) (Q : List ℚ) (ε ε' m0 : ℚ)
    (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) && decide (c.r < d.a) && decide (16 + c.r ≤ d.a + d.n) &&
    decide (stirRemQ d c.r ≤ 1) &&
    match tm c (scaledExpr d k l2lo l2hi) with
    | some T => relOk c.r T.p Q (T.e + 2 * stirRemQ d c.r * (absSum c.r T.p + T.e)) 1 ε ε' m0 depth
    | none => false

theorem gammaScaledOk_sound (c : Cfg) (d : LgData) (k : ℕ) (l2lo l2hi : ℚ) (Q : List ℚ)
    (ε ε' m0 : ℚ) (depth : ℕ) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi)
    (h : gammaScaledOk c d k l2lo l2hi Q ε ε' m0 depth = true) {t : ℝ} (ht : |t| ≤ c.r) :
    |Gamma (d.a + t) / 2 ^ k - eval Q t| ≤ ε' * (Gamma (d.a + t) / 2 ^ k) := by
  simp only [gammaScaledOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hr, ha⟩, hY⟩, hρ⟩, hm⟩ := h
  have hrr : (c.r : ℝ) < d.a := by exact_mod_cast ha
  have htr := abs_le.mp ht
  have hpos : 0 < Gamma (d.a + t) / 2 ^ k := div_pos (Gamma_pos_of_pos (by linarith)) (by positivity)
  cases hT : tm c (scaledExpr d k l2lo l2hi) with
  | none => simp [hT] at hm
  | some T =>
    simp only [hT] at hm
    have hρr : stirRem d c.r ≤ 1 := by rw [stirRem_eq]; exact_mod_cast hρ
    have hb := relOk_sound c.r T.p Q _ 1 ε ε' m0 depth hm (fun _ => True)
      (fun t => Gamma (d.a + t) / 2 ^ k) (fun t ht _ => by
        have := scaled_model d c hr hpi ha hY hρr k l2lo l2hi hT ht
        rw [stirRem_eq] at this
        push_cast
        exact this) t ht trivial
    rwa [abs_of_pos hpos] at hb

#print axioms scaled_model
#print axioms gammaScaledOk_sound

end LeanExe.ProofKit.GammaScaled
