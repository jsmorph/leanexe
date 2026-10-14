import LeanExe.ProofKit.GammaDD

/-!
Relative bounds for CORE-MATH's polynomials for `lgamma`.  `relOk r p P e σ ε ε' m0` is a kernel
check that a model `p`, within `e` of a function `f` on `[-r, r]`, satisfies `σ p ≥ m0` and
`|p - P| ≤ ε σ p` there (`PolyChecks.abs_le_weighted`), with `e (1 + ε) ≤ (ε' - ε) (m0 - e)`;
`relOk_sound` turns it into `|f t - P t| ≤ ε' |f t|`.  The model is the Taylor model of `lgamma`
(`lgammaRelOk`), of `lgamma` times an expression `G` such as `1/(1 - x)` (`lgammaMulRelOk`), or of
the divided difference at a zero (`ddRelOk`), each with its own bound `e`.
-/

namespace LeanExe.ProofKit.GammaRel

open Real Finset PolyBound PolyChecks TaylorModel GammaBasic GammaStirling GammaModels GammaFits
  GammaDD

/-- The weighted check of `P` against the model `p` with error `e`, sign `σ`, and floor `m0`. -/
def relOk (r : ℚ) (p P : List ℚ) (e σ ε ε' m0 : ℚ) (depth : ℕ) : Bool :=
  let A := subP p P
  let W := scaleP σ p
  let q1 := subP A (scaleP ε W)
  let q2 := addP A (scaleP ε W)
  let q3 := addP W [-m0]
  decide (0 ≤ r) && decide (σ = 1 ∨ σ = -1) && decide (0 ≤ ε) &&
    check (addP q1 [absSum r q1]) (-r) r (absSum r q1) depth &&
    check (subP q2 [absSum r q2]) (-r) r (absSum r q2) depth &&
    check (subP q3 [absSum r q3]) (-r) r (absSum r q3) depth &&
    decide (0 < m0 - e) && decide (e * (1 + ε) ≤ (ε' - ε) * (m0 - e))

theorem relOk_sound (r : ℚ) (p P : List ℚ) (e σ ε ε' m0 : ℚ) (depth : ℕ)
    (h : relOk r p P e σ ε ε' m0 depth = true) (D : ℝ → Prop) (f : ℝ → ℝ)
    (hf : ∀ t : ℝ, |t| ≤ r → D t → |f t - eval p t| ≤ e) :
    ∀ t : ℝ, |t| ≤ r → D t → |f t - eval P t| ≤ ε' * |f t| := by
  intro t ht hD
  simp only [relOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hr, hσ⟩, hε⟩, h1⟩, h2⟩, h3⟩, hm⟩, he⟩ := h
  have htr := abs_le.mp ht
  have hlo : ((-r : ℚ) : ℝ) ≤ t := by push_cast; linarith
  have hhi : t ≤ (r : ℝ) := htr.2
  have hw := abs_le_weighted (subP p P) (scaleP σ p) ε (-r) r _ _
    (bounded_of_check _ _ _ _ _ h1) (bounded_of_check _ _ _ _ _ h2) t hlo hhi
  have hm0 := nonneg_of_bounded _ (-r) r _ (bounded_of_check _ _ _ _ _ h3) t hlo hhi
  rw [eval_addP, eval_scaleP] at hm0
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hm0
  rw [eval_subP, eval_scaleP] at hw
  have hft := hf t ht hD
  have hεr : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have hmr : (0 : ℝ) < m0 - e := by exact_mod_cast hm
  have her : (e : ℝ) * (1 + ε) ≤ (ε' - ε) * (m0 - e) := by exact_mod_cast he
  push_cast at hm0 hmr her
  have he0 : (0 : ℝ) ≤ e := (abs_nonneg _).trans hft
  have key : (σ : ℝ) * f t ≥ m0 - e ∧ |f t| = σ * f t ∧ (σ : ℝ) * eval p t ≤ σ * f t + e := by
    obtain ⟨hl, hu⟩ := abs_le.mp hft
    rcases hσ with h | h
    · subst h
      push_cast at hm0 ⊢
      refine ⟨by linarith, ?_, by linarith⟩
      rw [abs_of_pos (by linarith), one_mul]
    · subst h
      push_cast at hm0 ⊢
      refine ⟨by linarith, ?_, by linarith⟩
      rw [abs_of_neg (by linarith)]
      ring
  obtain ⟨hσ1, habs, hwp⟩ := key
  have hε' : (0 : ℝ) ≤ ε' - ε := by
    by_contra hn
    have hneg := not_le.mp hn
    have : ((ε' : ℝ) - ε) * (m0 - e) < 0 := mul_neg_of_neg_of_pos hneg hmr
    nlinarith
  have hstep := mul_le_mul_of_nonneg_left hwp hεr
  have hstep2 := mul_le_mul_of_nonneg_left (show (m0 : ℝ) - e ≤ |f t| by rw [habs]; linarith) hε'
  calc |f t - eval P t| = |(f t - eval p t) + (eval p t - eval P t)| := by ring_nf
    _ ≤ |f t - eval p t| + |eval p t - eval P t| := abs_add_le _ _
    _ ≤ e + ε * (σ * eval p t) := add_le_add hft hw
    _ ≤ e + ε * (σ * f t + e) := by linarith
    _ = ε * |f t| + e * (1 + ε) := by rw [habs]; ring
    _ ≤ ε * |f t| + (ε' - ε) * |f t| := by linarith
    _ = ε' * |f t| := by ring

/-- The relative check of `P` against `lgamma (a + t)`. -/
def lgammaRelOk (c : Cfg) (d : LgData) (P : List ℚ) (σ ε ε' m0 : ℚ) (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) && decide (c.r < d.a) && decide (16 + c.r ≤ d.a + d.n) &&
    match tm c (lgammaExpr d) with
    | some T => relOk c.r T.p P (T.e + stirRemQ d c.r) σ ε ε' m0 depth
    | none => false

theorem lgammaRelOk_sound (c : Cfg) (d : LgData) (P : List ℚ) (σ ε ε' m0 : ℚ) (depth : ℕ)
    (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (h : lgammaRelOk c d P σ ε ε' m0 depth = true) {t : ℝ}
    (ht : |t| ≤ c.r) : |lgamma (d.a + t) - eval P t| ≤ ε' * |lgamma (d.a + t)| := by
  simp only [lgammaRelOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, ha⟩, hY⟩, hm⟩ := h
  cases hT : tm c (lgammaExpr d) with
  | none => simp [hT] at hm
  | some T =>
    simp only [hT] at hm
    refine relOk_sound c.r T.p P _ σ ε ε' m0 depth hm (fun _ => True)
      (fun t => lgamma (d.a + t)) (fun t ht _ => ?_) t ht trivial
    have hb := lgamma_model d c hr hpi ha hY hT ht
    rw [stirRem_eq] at hb
    push_cast
    exact hb

/-- The relative check of `P` against `lgamma (a + t) · G t`, with `G` within `bG` of zero. -/
def lgammaMulRelOk (c : Cfg) (d : LgData) (G : Expr) (P : List ℚ) (σ ε ε' m0 : ℚ)
    (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) && decide (c.r < d.a) && decide (16 + c.r ≤ d.a + d.n) &&
    match tm c G, tm c (.mul (lgammaExpr d) G) with
    | some TG, some T => relOk c.r T.p P (T.e + stirRemQ d c.r * bnd c TG) σ ε ε' m0 depth
    | _, _ => false

theorem lgammaMulRelOk_sound (c : Cfg) (d : LgData) (G : Expr) (P : List ℚ) (σ ε ε' m0 : ℚ)
    (depth : ℕ) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi)
    (h : lgammaMulRelOk c d G P σ ε ε' m0 depth = true) {t : ℝ} (ht : |t| ≤ c.r) :
    |lgamma (d.a + t) * G.eval t - eval P t| ≤ ε' * |lgamma (d.a + t) * G.eval t| := by
  simp only [lgammaMulRelOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, ha⟩, hY⟩, hm⟩ := h
  cases hTG : tm c G with
  | none => simp [hTG] at hm
  | some TG =>
    cases hT : tm c (.mul (lgammaExpr d) G) with
    | none => simp [hTG, hT] at hm
    | some T =>
      simp only [hTG, hT] at hm
      refine relOk_sound c.r T.p P _ σ ε ε' m0 depth hm (fun _ => True)
        (fun t => lgamma (d.a + t) * G.eval t) (fun t ht _ => ?_) t ht trivial
      have h1 := lgamma_sub_expr_le d hr ha hY ht
      rw [stirRem_eq] at h1
      have h2 := tm_sound c hr hpi _ hT t ht
      have hGb := approx_bnd c hr (tm_sound c hr hpi _ hTG) t ht
      have h2' : |(lgammaExpr d).eval t * G.eval t - eval T.p t| ≤ T.e := h2
      have hρ : (0 : ℝ) ≤ stirRemQ d c.r := (abs_nonneg _).trans h1
      push_cast
      calc |lgamma (d.a + t) * G.eval t - eval T.p t|
          = |(lgamma (d.a + t) - (lgammaExpr d).eval t) * G.eval t +
              ((lgammaExpr d).eval t * G.eval t - eval T.p t)| := by ring_nf
        _ ≤ |(lgamma (d.a + t) - (lgammaExpr d).eval t) * G.eval t| +
              |(lgammaExpr d).eval t * G.eval t - eval T.p t| := abs_add_le _ _
        _ ≤ stirRemQ d c.r * bnd c TG + T.e := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul h1 hGb (abs_nonneg _) hρ) h2'
        _ = _ := by ring

/-- The relative check of `P` against the divided difference at `x0`, for `|s0 + t| ≥ τ`. -/
def ddRelOk (c : Cfg) (d : DDData) (s0 R τ : ℚ) (P : List ℚ) (σ ε ε' m0 : ℚ) (depth : ℕ) :
    Bool :=
  decide (0 ≤ c.r) && decide (qabs s0 + c.r ≤ R) && decide (R < d.x0) &&
    decide (16 + R ≤ d.x0 + d.n) && decide (0 < τ) &&
    match tm c (ddExpr d s0) with
    | some T => relOk c.r T.p P (T.e + 2 * stirRemQ d.lg R / τ) σ ε ε' m0 depth
    | none => false

theorem ddRelOk_sound (c : Cfg) (d : DDData) (s0 R τ : ℚ) (P : List ℚ) (σ ε ε' m0 : ℚ)
    (depth : ℕ) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi)
    (h : ddRelOk c d s0 R τ P σ ε ε' m0 depth = true) {t : ℝ} (ht : |t| ≤ c.r)
    (hτ : (τ : ℝ) ≤ |s0 + t|) :
    |(lgamma (d.x0 + (s0 + t)) - lgamma d.x0) / (s0 + t) - eval P t| ≤
      ε' * |(lgamma (d.x0 + (s0 + t)) - lgamma d.x0) / (s0 + t)| := by
  simp only [ddRelOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hr, hR⟩, ha⟩, hY⟩, hτ0⟩, hm⟩ := h
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ0
  cases hT : tm c (ddExpr d s0) with
  | none => simp [hT] at hm
  | some T =>
    simp only [hT] at hm
    refine relOk_sound c.r T.p P _ σ ε ε' m0 depth hm (fun t => (τ : ℝ) ≤ |s0 + t|)
      (fun t => (lgamma (d.x0 + (s0 + t)) - lgamma d.x0) / (s0 + t)) (fun t ht hτt => ?_) t ht hτ
    have hs : (s0 : ℝ) + t ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hτt
      linarith
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
      div_le_div_of_nonneg_left (by positivity) hτr hτt
    push_cast
    linarith

#print axioms relOk_sound
#print axioms lgammaRelOk_sound
#print axioms lgammaMulRelOk_sound
#print axioms ddRelOk_sound

end LeanExe.ProofKit.GammaRel
