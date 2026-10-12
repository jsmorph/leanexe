import LeanExe.ProofKit.GammaFits

/-!
Divided differences of `lgamma`, for the relative accuracy of CORE-MATH's polynomials next to a
zero of `lgamma`.  For a base point `x0 > 0` with `n` shifts, `Y = x0 + n`, and `s = s0 + t`,
`ddExpr d s0` is the expression in `t`

  `(Y + s - 1/2)/Y · L (s/Y) + log Y - 1 - v V Q (v) - Σ k < n, L (s/(x0 + k))/(x0 + k)`,

where `L u = log (1 + u)/u`, `v = 1/(Y + s)`, `V = 1/Y`, `Q = ddPoly V stirCoeffs 0` with
`(v - V) Q (v) = S (v) - S (V)` for Stirling's series `S` in `v` (`ddPoly_eval`), and the last term
is `Σ k < n, L (s/(x0 + k))/(x0 + k)`, the shifts' logarithms one at a time (`ddShift`), each with
an argument below `|s|/(x0 + k)`.  For `s ≠ 0` the expression equals the divided
difference `(E s - E 0)/s` of the model `E = lgammaExpr` (`ddExpr_eval`), so that
`(lgamma (x0 + s) - lgamma x0)/s` differs from it by at most `2 ρ / |s|` with Stirling's remainder
`ρ` (`lgamma_dd`).  `ddPieceOk` checks a polynomial against the Taylor model of `ddExpr`.
-/

namespace LeanExe.ProofKit.GammaDD

open Real Finset PolyBound PolyChecks PolyCalculus TaylorModel GammaBasic GammaStirling GammaModels
  GammaFits

theorem length_scaleP (c : ℚ) (p : List ℚ) : (scaleP c p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [scaleP, ih]

/-- `[V ^ k, V ^ (k - 1), …, 1]`, the coefficients of `Σ j ≤ k, V ^ (k - j) v ^ j`. -/
def geomList (V : ℚ) : ℕ → List ℚ
  | 0 => [1]
  | k + 1 => scaleP V (geomList V k) ++ [1]

theorem geomList_length (V : ℚ) (k : ℕ) : (geomList V k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [geomList, length_scaleP, ih]

theorem geomList_eval (V : ℚ) (k : ℕ) (v : ℝ) :
    (v - V) * eval (geomList V k) v = v ^ (k + 1) - (V : ℝ) ^ (k + 1) := by
  induction k with
  | zero => simp [geomList]
  | succ k ih =>
    rw [geomList, TaylorRemainder.eval_append, eval_scaleP, length_scaleP, geomList_length]
    simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one, mul_one]
    linear_combination (V : ℝ) * ih

/-- `Σ i, cs i · geomList V (2 (k + i))`. -/
def ddPoly (V : ℚ) : List ℚ → ℕ → List ℚ
  | [], _ => []
  | c :: cs, k => addP (scaleP c (geomList V (2 * k))) (ddPoly V cs (k + 1))

/-- `v ^ (2 k + 1) eval cs (v ^ 2)`, the tail of Stirling's series in `v = 1/y`. -/
noncomputable def sv (cs : List ℚ) (k : ℕ) (v : ℝ) : ℝ := v ^ (2 * k + 1) * eval cs (v ^ 2)

theorem ddPoly_eval (V : ℚ) (v : ℝ) :
    ∀ (cs : List ℚ) (k : ℕ), (v - V) * eval (ddPoly V cs k) v = sv cs k v - sv cs k V := by
  intro cs
  induction cs with
  | nil => intro k; simp [ddPoly, sv]
  | cons c cs ih =>
    intro k
    have hsplit : ∀ y : ℝ, sv (c :: cs) k y = c * y ^ (2 * k + 1) + sv cs (k + 1) y := by
      intro y
      simp only [sv, eval_cons]
      ring
    rw [ddPoly, eval_addP, eval_scaleP, hsplit, hsplit, mul_add]
    have hg := geomList_eval V (2 * k) v
    linear_combination (c : ℝ) * hg + ih (k + 1)

theorem series_eq_sv (cs : List ℚ) (y : ℝ) : series cs y = sv cs 0 y⁻¹ := by
  simp [series, sv]

theorem dd_lead {Y s : ℝ} (hY : 0 < Y) (hYs : 0 < Y + s) (hs : s ≠ 0) :
    (Y + s - 1 / 2) / Y * (Real.log (1 + s / Y) / (s / Y)) + Real.log Y - 1 =
      (lead (Y + s) - lead Y) / s := by
  have hlog : Real.log (1 + s / Y) = Real.log (Y + s) - Real.log Y := by
    rw [← Real.log_div hYs.ne' hY.ne']
    congr 1
    field_simp
  rw [hlog, lead, lead]
  field_simp
  ring

theorem dd_series {Y s : ℝ} (hY : 0 < Y) (hYs : 0 < Y + s) (hs : s ≠ 0) (V : ℚ)
    (hV : (V : ℝ) = Y⁻¹) :
    -((Y + s)⁻¹ * V * eval (ddPoly V stirCoeffs 0) (Y + s)⁻¹) =
      (series stirCoeffs (Y + s) - series stirCoeffs Y) / s := by
  have h := ddPoly_eval V (Y + s)⁻¹ stirCoeffs 0
  rw [series_eq_sv, series_eq_sv, ← hV, ← h, hV]
  field_simp
  ring

/-- The leading part of the divided difference. -/
def ddLead (Y s0 : ℚ) (ly : LogData) (l2lo l2hi : ℚ) : Expr :=
  .add (.mul (.poly [(Y + s0 - 1 / 2) / Y, 1 / Y]) (.log1pDiv (.poly [s0 / Y, 1 / Y])))
    (.add (logExpr Y ly l2lo l2hi) (.const (-1)))

/-- The series part of the divided difference. -/
def ddSer (Y s0 : ℚ) : Expr :=
  .neg (.mul (.mul (.inv (.poly [Y + s0, 1])) (.const (1 / Y)))
    (.polyOf (ddPoly (1 / Y) stirCoeffs 0) (.inv (.poly [Y + s0, 1]))))

/-- The shift part of the divided difference, one term `log (1 + s/(x0 + k))/s` for each of the
first `n` shifts, so that each logarithm's argument stays below `|s|/(x0 + k)`. -/
def ddShift (x0 : ℚ) (s0 : ℚ) : ℕ → Expr
  | 0 => .const 0
  | k + 1 => .add (ddShift x0 s0 k)
      (.mul (.const (1 / (x0 + k))) (.log1pDiv (.poly [s0 / (x0 + k), 1 / (x0 + k)])))

theorem ddLead_eval (Y s0 : ℚ) (hYq : 0 < Y) (ly : LogData) (l2lo l2hi : ℚ) {t : ℝ}
    (hs : (s0 : ℝ) + t ≠ 0) (hYs : 0 < (Y : ℝ) + (s0 + t)) :
    (ddLead Y s0 ly l2lo l2hi).eval t = (lead (Y + (s0 + t)) - lead Y) / (s0 + t) := by
  have hY : (0 : ℝ) < Y := by exact_mod_cast hYq
  simp only [ddLead, Expr.eval, eval_cons, eval_nil, mul_zero, add_zero]
  rw [logExpr_eval _ hYq]
  have hU : ((s0 / Y : ℚ) : ℝ) + t * ((1 / Y : ℚ) : ℝ) = (s0 + t) / Y := by
    push_cast
    ring
  have hA : (((Y + s0 - 1 / 2) / Y : ℚ) : ℝ) + t * ((1 / Y : ℚ) : ℝ) =
      (Y + (s0 + t) - 1 / 2) / Y := by
    push_cast
    ring
  rw [hU, hA, ite_eq_right (div_ne_zero hs hY.ne')]
  have h := dd_lead hY hYs hs
  push_cast
  linarith

theorem ddSer_eval (Y s0 : ℚ) (hYq : 0 < Y) {t : ℝ} (hs : (s0 : ℝ) + t ≠ 0)
    (hYs : 0 < (Y : ℝ) + (s0 + t)) :
    (ddSer Y s0).eval t =
      (series stirCoeffs (Y + (s0 + t)) - series stirCoeffs Y) / (s0 + t) := by
  have hY : (0 : ℝ) < Y := by exact_mod_cast hYq
  simp only [ddSer, Expr.eval, eval_cons, eval_nil, mul_zero, add_zero]
  have hv : ((Y + s0 : ℚ) : ℝ) + t * ((1 : ℚ) : ℝ) = Y + (s0 + t) := by
    push_cast
    ring
  rw [hv]
  have h := dd_series hY hYs hs (1 / Y) (by push_cast; ring)
  rw [← h]

theorem ddShift_eval (x0 : ℚ) (hx0 : 0 < x0) (s0 : ℚ) {t : ℝ} (hs : (s0 : ℝ) + t ≠ 0)
    (hpos : 0 < (x0 : ℝ) + (s0 + t)) (n : ℕ) :
    (ddShift x0 s0 n).eval t =
      (∑ k ∈ range n, Real.log (x0 + k + (s0 + t)) - ∑ k ∈ range n, Real.log (x0 + k)) /
        (s0 + t) := by
  have hx0r : (0 : ℝ) < x0 := by exact_mod_cast hx0
  induction n with
  | zero => simp [ddShift, Expr.eval]
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hxk : (0 : ℝ) < x0 + k := by linarith
    have hxks : (0 : ℝ) < x0 + k + (s0 + t) := by linarith
    have hxkq : (0 : ℚ) < x0 + k := by exact_mod_cast hxk
    have hu : ((s0 / (x0 + k) : ℚ) : ℝ) + t * ((1 / (x0 + k) : ℚ) : ℝ) = (s0 + t) / (x0 + k) := by
      push_cast
      field_simp
    have hterm : ((1 / (x0 + k) : ℚ) : ℝ) *
        (if (s0 + t) / (x0 + k) = 0 then 1 else
          Real.log (1 + (s0 + t) / (x0 + k)) / ((s0 + t) / (x0 + k))) =
        (Real.log (x0 + k + (s0 + t)) - Real.log (x0 + k)) / (s0 + t) := by
      rw [ite_eq_right (div_ne_zero hs hxk.ne')]
      have hl : Real.log (1 + (s0 + t) / (x0 + k)) =
          Real.log (x0 + k + (s0 + t)) - Real.log (x0 + k) := by
        rw [← Real.log_div hxks.ne' hxk.ne']
        congr 1
        rw [eq_div_iff hxk.ne', add_mul, div_mul_cancel₀ _ hxk.ne']
        ring
      rw [hl]
      push_cast
      field_simp
    simp only [ddShift, Expr.eval, eval_cons, eval_nil, mul_zero, add_zero]
    rw [ih, hu, hterm, Finset.sum_range_succ, Finset.sum_range_succ, ← add_div]
    congr 1
    ring

/-- The data of a divided difference at `x0` with `n` shifts. -/
structure DDData where
  x0 : ℚ
  n : ℕ
  l2lo : ℚ
  l2hi : ℚ
  ly : LogData

/-- The divided-difference expression in `t`, at `s = s0 + t`. -/
def ddExpr (d : DDData) (s0 : ℚ) : Expr :=
  Expr.sub (.add (ddLead (d.x0 + d.n) s0 d.ly d.l2lo d.l2hi) (ddSer (d.x0 + d.n) s0))
    (ddShift d.x0 s0 d.n)

/-- The model `lead (Y + s) + series (Y + s) - Σ k < n, log (x0 + k + s)` without its constant. -/
noncomputable def ddE (d : DDData) (s : ℝ) : ℝ :=
  lead ((d.x0 : ℝ) + d.n + s) + series stirCoeffs ((d.x0 : ℝ) + d.n + s) -
    ∑ k ∈ range d.n, Real.log (d.x0 + k + s)

theorem ddExpr_eval (d : DDData) (hx0 : 0 < d.x0) (s0 : ℚ) {t : ℝ} (hs : (s0 : ℝ) + t ≠ 0)
    (hpos : 0 < (d.x0 : ℝ) + (s0 + t)) :
    (ddExpr d s0).eval t = (ddE d (s0 + t) - ddE d 0) / (s0 + t) := by
  have hx0r : (0 : ℝ) < d.x0 := by exact_mod_cast hx0
  have hn : (0 : ℝ) ≤ d.n := Nat.cast_nonneg _
  have hYq : (0 : ℚ) < d.x0 + d.n := by
    have : (0 : ℚ) ≤ d.n := Nat.cast_nonneg _
    linarith
  have hYs : (0 : ℝ) < ((d.x0 + d.n : ℚ) : ℝ) + (s0 + t) := by push_cast; linarith
  simp only [ddExpr, Expr.sub, Expr.eval]
  rw [ddLead_eval _ _ hYq _ _ _ hs hYs, ddSer_eval _ _ hYq hs hYs, ddShift_eval _ hx0 _ hs hpos]
  simp only [ddE, add_zero]
  push_cast
  field_simp
  ring

/-- The data `d` as a model of `lgamma`; the logarithm of the shift product is not used. -/
def DDData.lg (d : DDData) : LgData := ⟨d.x0, d.n, d.l2lo, d.l2hi, d.ly, ⟨0, 0, 0⟩⟩

theorem lgammaExpr_lg (d : DDData) (hx0 : 0 < d.x0) {s : ℝ} (hs : 0 < (d.x0 : ℝ) + s) :
    (lgammaExpr d.lg).eval s = ddE d s := by
  rw [lgammaExpr_eval d.lg hx0 hs]
  rfl

theorem lgamma_dd (d : DDData) (c : Cfg) (hr : 0 ≤ c.r) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi)
    (s0 R : ℚ) (hR : qabs s0 + c.r ≤ R) (ha : R < d.x0) (hY : 16 + R ≤ d.x0 + d.n) {T : TM}
    (hT : tm c (ddExpr d s0) = some T) {t : ℝ} (ht : |t| ≤ c.r) (hs : (s0 : ℝ) + t ≠ 0) :
    |(lgamma (d.x0 + (s0 + t)) - lgamma d.x0) / (s0 + t) - eval T.p t| ≤
      T.e + 2 * stirRem d.lg R / |s0 + t| := by
  have hRr : (qabs s0 : ℝ) + c.r ≤ R := by exact_mod_cast hR
  rw [qabs_cast] at hRr
  have hR0 : 0 ≤ R := by
    have : (0 : ℝ) ≤ R := le_trans (add_nonneg (abs_nonneg _) (by exact_mod_cast hr)) hRr
    exact_mod_cast this
  have hst : |(s0 : ℝ) + t| ≤ R := (abs_add_le _ _).trans (by linarith)
  have hx0 : 0 < d.x0 := lt_of_le_of_lt hR0 ha
  have hxr : (R : ℝ) < d.x0 := by exact_mod_cast ha
  have hpos : 0 < (d.x0 : ℝ) + (s0 + t) := by linarith [neg_abs_le ((s0 : ℝ) + t)]
  have hR0r : (0 : ℝ) ≤ R := by exact_mod_cast hR0
  have hpos0 : 0 < (d.x0 : ℝ) + 0 := by linarith
  have h1 := lgamma_sub_expr_le d.lg hR0 ha hY hst
  have h0 := lgamma_sub_expr_le d.lg hR0 ha hY (t := 0) (by rw [abs_zero]; exact_mod_cast hR0)
  rw [lgammaExpr_lg d hx0 hpos] at h1
  rw [lgammaExpr_lg d hx0 hpos0, add_zero] at h0
  change |lgamma ((d.x0 : ℝ) + ((s0 : ℝ) + t)) - ddE d ((s0 : ℝ) + t)| ≤ stirRem d.lg R at h1
  change |lgamma (d.x0 : ℝ) - ddE d 0| ≤ stirRem d.lg R at h0
  have hE := ddExpr_eval d hx0 s0 hs hpos
  have hTM := tm_sound c hr hpi _ hT t ht
  rw [hE] at hTM
  have hsa : 0 < |(s0 : ℝ) + t| := abs_pos.mpr hs
  have hsplit : (lgamma (d.x0 + (s0 + t)) - lgamma d.x0) / (s0 + t) - eval T.p t =
      ((lgamma (d.x0 + (s0 + t)) - ddE d (s0 + t)) - (lgamma d.x0 - ddE d 0)) / (s0 + t) +
        ((ddE d (s0 + t) - ddE d 0) / (s0 + t) - eval T.p t) := by
    field_simp
    ring
  rw [hsplit]
  have hfirst : |((lgamma (d.x0 + (s0 + t)) - ddE d (s0 + t)) - (lgamma d.x0 - ddE d 0)) /
      (s0 + t)| ≤ 2 * stirRem d.lg R / |s0 + t| := by
    rw [abs_div, div_le_div_iff_of_pos_right hsa]
    have h3 := abs_sub (lgamma (d.x0 + (s0 + t)) - ddE d (s0 + t)) (lgamma d.x0 - ddE d 0)
    linarith
  have h4 := abs_add_le
    (((lgamma (d.x0 + (s0 + t)) - ddE d (s0 + t)) - (lgamma d.x0 - ddE d 0)) / (s0 + t))
    ((ddE d (s0 + t) - ddE d 0) / (s0 + t) - eval T.p t)
  linarith

/-- The kernel check that `P` approximates the divided difference within `ε` for `|t| ≤ r` and
`|s0 + t| ≥ τ`. -/
def ddPieceOk (c : Cfg) (d : DDData) (s0 R τ : ℚ) (P : List ℚ) (ε : ℚ) (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) && decide (qabs s0 + c.r ≤ R) && decide (R < d.x0) &&
    decide (16 + R ≤ d.x0 + d.n) && decide (0 < τ) &&
    match tm c (ddExpr d s0) with
    | some T => check (subP T.p P) (-c.r) c.r (ε - T.e - 2 * stirRemQ d.lg R / τ) depth
    | none => false

theorem ddPieceOk_sound (c : Cfg) (d : DDData) (s0 R τ : ℚ) (P : List ℚ) (ε : ℚ) (depth : ℕ)
    (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (h : ddPieceOk c d s0 R τ P ε depth = true) {t : ℝ}
    (ht : |t| ≤ c.r) (hτ : (τ : ℝ) ≤ |s0 + t|) :
    |(lgamma (d.x0 + (s0 + t)) - lgamma d.x0) / (s0 + t) - eval P t| ≤ ε := by
  simp only [ddPieceOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hr, hR⟩, ha⟩, hY⟩, hτ0⟩, hm⟩ := h
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ0
  have hs : (s0 : ℝ) + t ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hτ
    linarith
  cases hT : tm c (ddExpr d s0) with
  | none => simp [hT] at hm
  | some T =>
    simp only [hT] at hm
    have htr := abs_le.mp ht
    have hc := check_sound _ _ _ _ _ hm t (by push_cast; linarith) (by linarith)
    rw [eval_subP] at hc
    have hd := lgamma_dd d c hr hpi s0 R hR ha hY hT ht hs
    rw [stirRem_eq] at hd
    have hρ : (0 : ℝ) ≤ stirRemQ d.lg R := by
      have : (0 : ℚ) ≤ stirRemQ d.lg R := by
        unfold stirRemQ
        simp only [DDData.lg]
        apply div_nonneg (by norm_num)
        apply mul_nonneg (by norm_num)
        apply pow_nonneg
        linarith
      exact_mod_cast this
    have hdiv : 2 * (stirRemQ d.lg R : ℝ) / |s0 + t| ≤ 2 * stirRemQ d.lg R / τ :=
      div_le_div_of_nonneg_left (by positivity) hτr hτ
    push_cast at hc
    calc _ = |((lgamma (d.x0 + (s0 + t)) - lgamma d.x0) / (s0 + t) - eval T.p t) +
          (eval T.p t - eval P t)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith

#print axioms ddPoly_eval
#print axioms ddExpr_eval
#print axioms lgamma_dd
#print axioms ddPieceOk_sound

end LeanExe.ProofKit.GammaDD
