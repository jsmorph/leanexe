import LeanExe.ProofKit.TaylorModel
import LeanExe.ProofKit.GammaStirling

/-!
Taylor models of `lgamma` and `Γ` on intervals of positive numbers.  For a center `a > r` and
`n` shifts with `Y = a + n ≥ 16 + r`, `lgammaExpr` is the expression in `t`

  `(Y + t - 1/2) (log Y + log (1 + t/Y)) - (Y + t) + (log 2 + log π)/2 + S (Y + t)`
  `  - log (a (a + 1) ⋯ (a + n - 1)) - log (1 + w t)`,

where `S y = y⁻¹ Σ cs i y ^ -(2 i)` is Stirling's series with the twelve coefficients of
`GammaStirling.stirCoeffs` and `1 + w t = Π k < n, (1 + t/(a + k))`.  It equals
`lead (Y + t) + series (Y + t) - Σ k < n, log (a + k + t)` (`lgammaExpr_eval`), so by
`lgamma_add_nat` and `stirling_twelve` it differs from `lgamma (a + t)` by at most
`104001 / (25 (Y - r - 1) ^ 25)` (`lgamma_model`).  Each logarithm of a rational `q` is written as
`m log 2 + log (q / 2 ^ m)` with `q / 2 ^ m` near 1, and `log π` as `2 log 2 + log (1 + (π/4 - 1))`.
`gamma_model` turns a Taylor model of `exp (lgammaExpr)` into a bound on `Γ (a + t)`.
-/

namespace LeanExe.ProofKit.GammaModels

open Real Finset PolyBound PolyChecks PolyCalculus TaylorModel GammaBasic GammaStirling

/-- The coefficients of `Π k < n, (1 + t/(a + k))`. -/
def shiftPoly (a : ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => mulP (shiftPoly a n) [1, 1 / (a + n)]

/-- `Π k < n, (a + k)`. -/
def shiftProd (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => shiftProd a n * (a + n)

theorem eval_shiftPoly (a : ℚ) (n : ℕ) (t : ℝ) :
    eval (shiftPoly a n) t = ∏ k ∈ range n, (1 + t / ((a : ℝ) + k)) := by
  induction n with
  | zero => simp [shiftPoly]
  | succ n ih =>
    rw [shiftPoly, eval_mulP, ih, prod_range_succ]
    simp only [eval_cons, eval_nil, mul_zero, add_zero]
    push_cast
    ring

theorem shiftProd_cast (a : ℚ) (n : ℕ) :
    ((shiftProd a n : ℚ) : ℝ) = ∏ k ∈ range n, ((a : ℝ) + k) := by
  induction n with
  | zero => simp [shiftProd]
  | succ n ih =>
    rw [shiftProd, prod_range_succ, ← ih]
    push_cast
    ring

/-- `log q` as `m log 2 + log (q / 2 ^ m)`, with bounds on the second logarithm. -/
structure LogData where
  m : ℕ
  lo : ℚ
  hi : ℚ

/-- The expression `a - b`. -/
def Expr.sub (a b : Expr) : Expr := .add a (.neg b)

/-- `log q` from `d` and the bounds `l2lo`, `l2hi` on `log 2`. -/
def logExpr (q : ℚ) (d : LogData) (l2lo l2hi : ℚ) : Expr :=
  .add (.mul (.const d.m) (.logC 2 l2lo l2hi)) (.logC (q / 2 ^ d.m) d.lo d.hi)

theorem logExpr_eval (q : ℚ) (hq : 0 < q) (d : LogData) (l2lo l2hi : ℚ) (t : ℝ) :
    (logExpr q d l2lo l2hi).eval t = Real.log q := by
  simp only [logExpr, Expr.eval]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Real.log_div hq'.ne' (by positivity),
    Real.log_pow]
  push_cast
  ring

/-- `log π` as `2 log 2 + log (1 + (π/4 - 1))`. -/
def logPiExpr (l2lo l2hi : ℚ) : Expr :=
  .add (.mul (.const 2) (.logC 2 l2lo l2hi))
    (.log1p (.add (.mul (.const (1 / 4)) .pi) (.const (-1))))

theorem logPiExpr_eval (l2lo l2hi : ℚ) (t : ℝ) :
    (logPiExpr l2lo l2hi).eval t = Real.log π := by
  simp only [logPiExpr, Expr.eval]
  push_cast
  rw [show 1 + (1 / 4 * π + -1) = π / 2 ^ 2 by ring, Real.log_div pi_ne_zero (by norm_num),
    Real.log_pow]
  push_cast
  ring

/-- The parameters of a model of `lgamma (a + t)`. -/
structure LgData where
  a : ℚ
  n : ℕ
  l2lo : ℚ
  l2hi : ℚ
  ly : LogData
  lp : LogData

/-- The model expression of `lgamma (a + t)`. -/
def lgammaExpr (d : LgData) : Expr :=
  let Y : ℚ := d.a + d.n
  let lY := logExpr Y d.ly d.l2lo d.l2hi
  let u := Expr.poly [0, 1 / Y]
  let lead := Expr.sub (.mul (.poly [Y - 1 / 2, 1]) (.add lY (.log1p u)))
    (.add (.poly [Y, 1]) (.neg (.mul (.const (1 / 2))
      (.add (.logC 2 d.l2lo d.l2hi) (logPiExpr d.l2lo d.l2hi)))))
  let v := Expr.inv (.poly [Y, 1])
  let ser := Expr.mul v (.polyOf stirCoeffs (.mul v v))
  let shifts := Expr.add (logExpr (shiftProd d.a d.n) d.lp d.l2lo d.l2hi)
    (.log1p (.poly (subP (shiftPoly d.a d.n) [1])))
  Expr.sub (.add lead ser) shifts

theorem shiftProd_pos (a : ℚ) (ha : 0 < a) (n : ℕ) : 0 < shiftProd a n := by
  induction n with
  | zero => simp [shiftProd]
  | succ n ih =>
    rw [shiftProd]
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    exact mul_pos ih (by linarith)

theorem sum_log_shift (a : ℚ) (ha : 0 < a) (n : ℕ) {t : ℝ} (ht : 0 < (a : ℝ) + t) :
    ∑ k ∈ range n, Real.log (a + k + t) =
      Real.log ((shiftProd a n : ℚ) : ℝ) + Real.log (eval (shiftPoly a n) t) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hk : ∀ k ∈ range n, (0 : ℝ) < a + k := fun k _ => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hk2 : ∀ k ∈ range n, (0 : ℝ) < 1 + t / (a + k) := fun k hkr => by
    have h1 := hk k hkr
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have he : (1 : ℝ) + t / (a + k) = (a + k + t) / (a + k) := by
      rw [add_div, div_self h1.ne']
    rw [he]
    exact div_pos (by linarith) h1
  rw [shiftProd_cast, eval_shiftPoly, Real.log_prod (fun k hkr => (hk k hkr).ne'),
    Real.log_prod (fun k hkr => (hk2 k hkr).ne'), ← sum_add_distrib]
  refine sum_congr rfl fun k hkr => ?_
  rw [← Real.log_mul (hk k hkr).ne' (hk2 k hkr).ne']
  congr 1
  rw [mul_add, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ (hk k hkr).ne']

theorem lgammaExpr_eval (d : LgData) (ha : 0 < d.a) {t : ℝ} (ht : 0 < (d.a : ℝ) + t) :
    (lgammaExpr d).eval t = lead ((d.a : ℝ) + d.n + t) + series stirCoeffs ((d.a : ℝ) + d.n + t) -
      ∑ k ∈ range d.n, Real.log (d.a + k + t) := by
  have har : (0 : ℝ) < d.a := by exact_mod_cast ha
  have hY : (0 : ℝ) < (d.a : ℝ) + d.n := by
    have : (0 : ℝ) ≤ d.n := Nat.cast_nonneg _
    linarith
  have hYt : (0 : ℝ) < (d.a : ℝ) + d.n + t := by
    have : (0 : ℝ) ≤ d.n := Nat.cast_nonneg _
    linarith
  have hYq : (0 : ℚ) < d.a + d.n := by exact_mod_cast hY
  rw [sum_log_shift d.a ha d.n ht]
  simp only [lgammaExpr, Expr.sub, Expr.eval]
  rw [logExpr_eval _ hYq, logExpr_eval _ (shiftProd_pos d.a ha d.n), logPiExpr_eval]
  simp only [eval_cons, eval_nil, eval_subP, mul_zero, add_zero]
  push_cast
  simp only [zero_add, mul_one]
  have hlog : Real.log (1 + t * (1 / ((d.a : ℝ) + d.n))) =
      Real.log ((d.a : ℝ) + d.n + t) - Real.log ((d.a : ℝ) + d.n) := by
    rw [← Real.log_div hYt.ne' hY.ne']
    congr 1
    field_simp
  rw [hlog, lead, series, Real.log_mul two_ne_zero pi_ne_zero]
  ring_nf

/-- The bound `104001 / (25 (Y - r - 1) ^ 25)` on the remainder of Stirling's series at
`Y + t ≥ Y - r`. -/
noncomputable def stirRem (d : LgData) (r : ℚ) : ℝ := 104001 / (25 * ((d.a : ℝ) + d.n - r - 1) ^ 25)

theorem lgamma_sub_expr_le (d : LgData) {r : ℚ} (hr : 0 ≤ r) (ha : r < d.a)
    (hY : 16 + r ≤ d.a + d.n) {t : ℝ} (ht : |t| ≤ r) :
    |lgamma (d.a + t) - (lgammaExpr d).eval t| ≤ stirRem d r := by
  have hrr : (r : ℝ) < d.a := by exact_mod_cast ha
  have hYr : (16 : ℝ) + r ≤ d.a + d.n := by exact_mod_cast hY
  have htr := abs_le.mp ht
  have hpos : 0 < (d.a : ℝ) + t := by linarith
  have hda : 0 < d.a := lt_of_le_of_lt hr ha
  rw [lgammaExpr_eval d hda hpos]
  have hsum := lgamma_add_nat hpos d.n
  have hy16 : (16 : ℝ) ≤ (d.a : ℝ) + d.n + t := by linarith
  have hst := stirling_twelve hy16
  have hswap : (d.a : ℝ) + t + d.n = d.a + d.n + t := by ring
  rw [hswap] at hsum
  have hs : ∑ m ∈ range d.n, Real.log ((d.a : ℝ) + t + m) =
      ∑ k ∈ range d.n, Real.log ((d.a : ℝ) + k + t) :=
    sum_congr rfl fun k _ => by ring_nf
  rw [hs] at hsum
  have hmono : 104001 / (25 * ((d.a : ℝ) + d.n + t - 1) ^ 25) ≤ stirRem d r := by
    rw [stirRem]
    have hpos' : (0 : ℝ) < (d.a : ℝ) + d.n - r - 1 := by linarith
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 25
  calc |lgamma (d.a + t) - (lead ((d.a : ℝ) + d.n + t) + series stirCoeffs ((d.a : ℝ) + d.n + t) -
        ∑ k ∈ range d.n, Real.log ((d.a : ℝ) + k + t))|
      = |lgamma ((d.a : ℝ) + d.n + t) - lead ((d.a : ℝ) + d.n + t) -
          series stirCoeffs ((d.a : ℝ) + d.n + t)| := by
        rw [hsum]
        ring_nf
    _ ≤ _ := hst.trans hmono

/-- A Taylor model of `lgammaExpr` bounds `lgamma (a + t)`. -/
theorem lgamma_model (d : LgData) (c : Cfg) (hr : 0 ≤ c.r)
    (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (ha : c.r < d.a) (hY : 16 + c.r ≤ d.a + d.n)
    {T : TM} (hT : tm c (lgammaExpr d) = some T) {t : ℝ} (ht : |t| ≤ c.r) :
    |lgamma (d.a + t) - eval T.p t| ≤ T.e + stirRem d c.r := by
  have h1 := lgamma_sub_expr_le d hr ha hY ht
  have h2 := tm_sound c hr hpi (lgammaExpr d) hT t ht
  calc |lgamma (d.a + t) - eval T.p t|
      = |(lgamma (d.a + t) - (lgammaExpr d).eval t) + ((lgammaExpr d).eval t - eval T.p t)| := by
        ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

/-- A Taylor model of `exp (lgammaExpr)` bounds `Γ (a + t)`, when `stirRem d r ≤ 1`. -/
theorem gamma_model (d : LgData) (c : Cfg) (hr : 0 ≤ c.r)
    (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (ha : c.r < d.a) (hY : 16 + c.r ≤ d.a + d.n)
    (hρ : stirRem d c.r ≤ 1) {T : TM} (hT : tm c (.exp (lgammaExpr d)) = some T) {t : ℝ}
    (ht : |t| ≤ c.r) :
    |Gamma (d.a + t) - eval T.p t| ≤
      T.e + 2 * stirRem d c.r * (((absSum c.r T.p : ℚ) : ℝ) + T.e) := by
  have hrr : (c.r : ℝ) < d.a := by exact_mod_cast ha
  have htr := abs_le.mp ht
  have hpos : 0 < (d.a : ℝ) + t := by linarith
  have hG : Gamma (d.a + t) = Real.exp (lgamma (d.a + t)) :=
    (Real.exp_log (Gamma_pos_of_pos hpos)).symm
  have h1 := lgamma_sub_expr_le d hr ha hY ht
  have h2 := tm_sound c hr hpi _ hT t ht
  set E := (lgammaExpr d).eval t
  have hEb : Real.exp E ≤ ((absSum c.r T.p : ℚ) : ℝ) + T.e := by
    have h3 := abs_eval_le c.r hr T.p t ht
    have h4 : |Real.exp E - eval T.p t| ≤ T.e := h2
    have := le_abs_self (Real.exp E - eval T.p t)
    have := le_abs_self (eval T.p t)
    linarith
  have hd : |Real.exp (lgamma (d.a + t)) - Real.exp E| ≤ Real.exp E * (2 * stirRem d c.r) := by
    have hx : |lgamma (d.a + t) - E| ≤ 1 := h1.trans hρ
    have h5 := Real.abs_exp_sub_one_le hx
    have he : Real.exp (lgamma (d.a + t)) - Real.exp E =
        Real.exp E * (Real.exp (lgamma (d.a + t) - E) - 1) := by
      rw [mul_sub, ← Real.exp_add, mul_one]
      ring_nf
    rw [he, abs_mul, abs_of_pos (Real.exp_pos E)]
    exact mul_le_mul_of_nonneg_left (h5.trans (by linarith)) (Real.exp_pos E).le
  rw [hG]
  calc |Real.exp (lgamma (d.a + t)) - eval T.p t|
      = |(Real.exp (lgamma (d.a + t)) - Real.exp E) + (Real.exp E - eval T.p t)| := by ring_nf
    _ ≤ |Real.exp (lgamma (d.a + t)) - Real.exp E| + |Real.exp E - eval T.p t| := abs_add_le _ _
    _ ≤ Real.exp E * (2 * stirRem d c.r) + T.e :=
        add_le_add hd (show |Real.exp E - eval T.p t| ≤ T.e from h2)
    _ ≤ _ := by
        have hs : 0 ≤ stirRem d c.r := (abs_nonneg _).trans h1
        have := mul_le_mul_of_nonneg_left hEb (by linarith : (0 : ℝ) ≤ 2 * stirRem d c.r)
        linarith

/-- `stirRem` as a rational. -/
def stirRemQ (d : LgData) (r : ℚ) : ℚ := 104001 / (25 * (d.a + d.n - r - 1) ^ 25)

theorem stirRem_eq (d : LgData) (r : ℚ) : stirRem d r = stirRemQ d r := by
  unfold stirRem stirRemQ
  norm_cast

/-- The kernel check that `P` approximates `Γ (a + t)` within `ε` for `|t| ≤ r`. -/
def gammaPieceOk (c : Cfg) (d : LgData) (P : List ℚ) (ε : ℚ) (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) && decide (c.r < d.a) && decide (16 + c.r ≤ d.a + d.n) &&
    decide (stirRemQ d c.r ≤ 1) &&
    match tm c (.exp (lgammaExpr d)) with
    | some T => check (subP T.p P) (-c.r) c.r
        (ε - T.e - 2 * stirRemQ d c.r * (absSum c.r T.p + T.e)) depth
    | none => false

theorem gammaPieceOk_sound (c : Cfg) (d : LgData) (P : List ℚ) (ε : ℚ) (depth : ℕ)
    (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (h : gammaPieceOk c d P ε depth = true) {t : ℝ}
    (ht : |t| ≤ c.r) : |Gamma (d.a + t) - eval P t| ≤ ε := by
  simp only [gammaPieceOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hr, ha⟩, hY⟩, hρ⟩, hm⟩ := h
  cases hT : tm c (.exp (lgammaExpr d)) with
  | none => simp [hT] at hm
  | some T =>
    simp only [hT] at hm
    have htr := abs_le.mp ht
    have hc := check_sound _ _ _ _ _ hm t (by push_cast; linarith) (by linarith)
    rw [eval_subP] at hc
    have hρr : stirRem d c.r ≤ 1 := by rw [stirRem_eq]; exact_mod_cast hρ
    have hg := gamma_model d c hr hpi ha hY hρr hT ht
    rw [stirRem_eq] at hg
    push_cast at hc
    calc |Gamma (d.a + t) - eval P t|
        = |(Gamma (d.a + t) - eval T.p t) + (eval T.p t - eval P t)| := by ring_nf
      _ ≤ |Gamma (d.a + t) - eval T.p t| + |eval T.p t - eval P t| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- A checked piece for a polynomial `P` in a variable `x` with `Γ` at `base + x`, centered at
`x = ctr`. -/
theorem piece_bound (c : Cfg) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (d : LgData) (P : List ℚ)
    (ε : ℚ) (depth : ℕ) (base ctr : ℚ) (hctr : d.a = base + ctr)
    (h : gammaPieceOk c d (shift ctr P) ε depth = true) (t : ℝ) (ht : |t| ≤ c.r) :
    |Gamma (base + (ctr + t)) - eval P (ctr + t)| ≤ ε := by
  have hb := gammaPieceOk_sound c d _ ε depth hpi h ht
  rw [eval_shift, hctr] at hb
  push_cast at hb
  rw [← add_assoc]
  exact hb

/-- A property that holds on `K` pieces of radius `r` from `lo` holds on `[lo, lo + 2 r K]`. -/
theorem cover_pieces {K : ℕ} (hK : 0 < K) {lo r : ℝ} (hr : 0 < r) (Q : ℝ → Prop)
    (h : ∀ j < K, ∀ t : ℝ, |t| ≤ r → Q (lo + r * (2 * j + 1) + t)) :
    ∀ x : ℝ, lo ≤ x → x ≤ lo + 2 * r * K → Q x := by
  intro x hlo hhi
  set j0 := ⌊(x - lo) / (2 * r)⌋₊ with hj0
  have h2r : 0 < 2 * r := by linarith
  have hq0 : 0 ≤ (x - lo) / (2 * r) := div_nonneg (by linarith) h2r.le
  have hfl := Nat.floor_le hq0
  have hlt := Nat.lt_floor_add_one ((x - lo) / (2 * r))
  rw [← hj0] at hfl hlt
  rw [le_div_iff₀ h2r] at hfl
  rw [div_lt_iff₀ h2r] at hlt
  by_cases hjK : j0 < K
  · have hx : x = lo + r * (2 * j0 + 1) + (x - lo - r * (2 * j0 + 1)) := by ring
    rw [hx]
    apply h j0 hjK
    rw [abs_le]
    constructor <;> nlinarith
  · have hK1 : K - 1 < K := Nat.sub_lt hK one_pos
    have hKc : ((K - 1 : ℕ) : ℝ) = K - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have hge : (K : ℝ) ≤ j0 := by exact_mod_cast not_lt.mp hjK
    have hx : x = lo + r * (2 * ((K - 1 : ℕ) : ℝ) + 1) + (x - lo - r * (2 * ((K - 1 : ℕ) : ℝ) + 1)) := by
      ring
    rw [hx]
    apply h (K - 1) hK1
    rw [hKc, abs_le]
    constructor <;> nlinarith

#print axioms lgammaExpr_eval
#print axioms lgamma_model
#print axioms gamma_model
#print axioms gammaPieceOk_sound
#print axioms piece_bound
#print axioms cover_pieces

end LeanExe.ProofKit.GammaModels
