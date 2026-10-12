import LeanExe.ProofKit.GammaModels
import LeanExe.ProofKit.GammaThresholds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Bounds on `lgamma` against expressions, for CORE-MATH's Stirling fits and polynomial pieces.
`lgammaDiffOk c d F ε depth` is a kernel check that the Taylor model of `lgammaExpr d - F` stays
within `ε` less the model's error and Stirling's remainder, and `lgammaDiffOk_sound` turns it into
`|lgamma (a + t) - F t| ≤ ε` on `[-r, r]`.

CORE-MATH's `as_lgamma_asym` and `cr_lgamma` approximate `lgamma x` by
`fit C0 P x = (x - 1/2) (log x - 1) + C0 + x⁻¹ P (x⁻²)` with a constant `C0` near
`(log (2 π) - 1)/2` and a fitted polynomial `P`.  `fitExpr` writes `fit C0 P (a + t)` as an
expression in `t` (`fitExpr_eval`), so that `fit_piece` bounds a fit on a piece.  For `x ≥ 16`,
`fit_large` compares the fit with Stirling's series: `lgamma x - fit C0 P x` is the remainder of
`stirling_twelve`, plus `(log (2 π) - 1)/2 - C0`, plus `x⁻¹ (S - P) (x⁻²)` for the twelve
coefficients `S`, which `PolyBound.check` bounds on `[0, 1/256]`.
-/

namespace LeanExe.ProofKit.GammaFits

open Real Finset PolyBound PolyChecks TaylorModel GammaBasic GammaStirling GammaModels
  GammaThresholds RatExpLog

/-- Mathlib's 20-digit bounds on `π`, as rationals for `Cfg`. -/
def piLo20 : ℚ := 314159265358979323846 / 10 ^ 20

def piHi20 : ℚ := 314159265358979323847 / 10 ^ 20

theorem pi_bounds20 : (piLo20 : ℝ) ≤ π ∧ π ≤ piHi20 := by
  constructor
  · have := pi_gt_d20
    simp only [piLo20]
    push_cast
    norm_num at this ⊢
    linarith
  · have := pi_lt_d20
    simp only [piHi20]
    push_cast
    norm_num at this ⊢
    linarith

/-- The kernel check that `F` approximates `lgamma (a + t)` within `ε` for `|t| ≤ r`. -/
def lgammaDiffOk (c : Cfg) (d : LgData) (F : Expr) (ε : ℚ) (depth : ℕ) : Bool :=
  decide (0 ≤ c.r) && decide (c.r < d.a) && decide (16 + c.r ≤ d.a + d.n) &&
    match tm c (Expr.sub (lgammaExpr d) F) with
    | some T => check T.p (-c.r) c.r (ε - T.e - stirRemQ d c.r) depth
    | none => false

theorem lgammaDiffOk_sound (c : Cfg) (d : LgData) (F : Expr) (ε : ℚ) (depth : ℕ)
    (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (h : lgammaDiffOk c d F ε depth = true) {t : ℝ}
    (ht : |t| ≤ c.r) : |lgamma (d.a + t) - F.eval t| ≤ ε := by
  simp only [lgammaDiffOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, ha⟩, hY⟩, hm⟩ := h
  cases hT : tm c (Expr.sub (lgammaExpr d) F) with
  | none => simp [hT] at hm
  | some T =>
    simp only [hT] at hm
    have htr := abs_le.mp ht
    have hc := check_sound _ _ _ _ _ hm t (by push_cast; linarith) (by linarith)
    have h1 := lgamma_sub_expr_le d hr ha hY ht
    rw [stirRem_eq] at h1
    have h2 := tm_sound c hr hpi _ hT t ht
    have h3 : (Expr.sub (lgammaExpr d) F).eval t = (lgammaExpr d).eval t - F.eval t := by
      simp only [Expr.sub, Expr.eval]
      ring
    rw [h3] at h2
    push_cast at hc
    calc |lgamma (d.a + t) - F.eval t|
        = |(lgamma (d.a + t) - (lgammaExpr d).eval t) +
            (((lgammaExpr d).eval t - F.eval t) - eval T.p t) + eval T.p t| := by ring_nf
      _ ≤ |lgamma (d.a + t) - (lgammaExpr d).eval t| +
            |((lgammaExpr d).eval t - F.eval t) - eval T.p t| + |eval T.p t| :=
          abs_add_three _ _ _
      _ ≤ _ := by linarith

/-- The form of CORE-MATH's Stirling fits. -/
noncomputable def fit (C0 : ℚ) (P : List ℚ) (x : ℝ) : ℝ :=
  (x - 1 / 2) * (Real.log x - 1) + C0 + x⁻¹ * eval P (x⁻¹ ^ 2)

/-- `fit C0 P (a + t)` as an expression in `t`, with `log a` from `ld` and bounds on `log 2`. -/
def fitExpr (a : ℚ) (ld : LogData) (l2lo l2hi C0 : ℚ) (P : List ℚ) : Expr :=
  let lx := Expr.add (logExpr a ld l2lo l2hi) (.log1p (.poly [0, 1 / a]))
  let main := Expr.mul (.poly [a - 1 / 2, 1]) (.add lx (.const (-1)))
  let v := Expr.inv (.poly [a, 1])
  .add (.add main (.const C0)) (.mul v (.polyOf P (.mul v v)))

theorem fitExpr_eval (a : ℚ) (ha : 0 < a) (ld : LogData) (l2lo l2hi C0 : ℚ) (P : List ℚ) {t : ℝ}
    (ht : 0 < (a : ℝ) + t) : (fitExpr a ld l2lo l2hi C0 P).eval t = fit C0 P (a + t) := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  simp only [fitExpr, Expr.eval]
  rw [logExpr_eval _ ha]
  simp only [eval_cons, eval_nil, mul_zero, add_zero]
  push_cast
  simp only [zero_add, mul_one]
  have hlog : Real.log (1 + t * (1 / (a : ℝ))) = Real.log ((a : ℝ) + t) - Real.log a := by
    rw [← Real.log_div ht.ne' har.ne']
    congr 1
    field_simp
  rw [hlog, fit]
  ring_nf

theorem fit_piece (c : Cfg) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi) (d : LgData) (ld : LogData)
    (C0 : ℚ) (P : List ℚ) (ε : ℚ) (depth : ℕ)
    (h : lgammaDiffOk c d (fitExpr d.a ld d.l2lo d.l2hi C0 P) ε depth = true) (t : ℝ)
    (ht : |t| ≤ c.r) : |lgamma (d.a + t) - fit C0 P (d.a + t)| ≤ ε := by
  have hb := lgammaDiffOk_sound c d _ ε depth hpi h ht
  simp only [lgammaDiffOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hr : 0 ≤ c.r := h.1.1.1
  have ha : c.r < d.a := h.1.1.2
  have hda : 0 < d.a := lt_of_le_of_lt hr ha
  have hpos : 0 < (d.a : ℝ) + t := by
    have : (c.r : ℝ) < d.a := by exact_mod_cast ha
    have := (abs_le.mp ht).1
    linarith
  rw [fitExpr_eval d.a hda ld _ _ C0 P hpos] at hb
  exact hb

/-- Rational bounds on `(log (2 π) - 1)/2`. -/
def halfLog2PiLo : ℚ := (2 * log2Lo + logHalfPiLo - 1) / 2

def halfLog2PiHi : ℚ := (2 * log2Hi + logHalfPiHi - 1) / 2

theorem halfLog2Pi_bounds :
    (halfLog2PiLo : ℝ) ≤ (Real.log (2 * π) - 1) / 2 ∧
      (Real.log (2 * π) - 1) / 2 ≤ halfLog2PiHi := by
  have h1 := log_two_lo
  have h2 := log_two_hi
  have h3 := log_half_pi_lo
  have h4 := log_half_pi_hi
  rw [log_two_pi]
  simp only [halfLog2PiLo, halfLog2PiHi]
  push_cast
  constructor <;> linarith

/-- The kernel check that a fit is within `ε` of `lgamma` from 16 on: `δ` bounds `S - P` on
`[0, 1/256]`. -/
def fitLargeOk (C0 : ℚ) (P : List ℚ) (δ ε : ℚ) (depth : ℕ) : Bool :=
  check (subP stirCoeffs P) 0 (1 / 256) δ depth &&
    decide (max (qabs (halfLog2PiLo - C0)) (qabs (halfLog2PiHi - C0)) + δ / 16 +
      104001 / (25 * 15 ^ 25) ≤ ε)

theorem fit_large (C0 : ℚ) (P : List ℚ) (δ ε : ℚ) (depth : ℕ)
    (h : fitLargeOk C0 P δ ε depth = true) {x : ℝ} (hx : 16 ≤ x) :
    |lgamma x - fit C0 P x| ≤ ε := by
  simp only [fitLargeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hε⟩ := h
  have hx0 : 0 < x := by linarith
  have hi0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hinv : x⁻¹ ≤ 1 / 16 := by
    rw [inv_le_comm₀ hx0 (by norm_num)]
    norm_num
    linarith
  have hz1 : x⁻¹ ^ 2 ≤ ((1 / 256 : ℚ) : ℝ) := by
    have := pow_le_pow_left₀ hi0.le hinv 2
    push_cast
    norm_num at this ⊢
    linarith
  have he := check_sound _ 0 (1 / 256) δ depth hc (x⁻¹ ^ 2) (by push_cast; positivity) hz1
  rw [eval_subP] at he
  have hst := stirling_twelve hx
  have hrem : 104001 / (25 * (x - 1) ^ 25) ≤ (104001 / (25 * 15 ^ 25) : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 25
  obtain ⟨hb1, hb2⟩ := halfLog2Pi_bounds
  set Mq := max (qabs (halfLog2PiLo - C0)) (qabs (halfLog2PiHi - C0)) with hMq
  have hm1 : |(halfLog2PiLo : ℝ) - C0| ≤ Mq := by
    have h := (Rat.cast_le (K := ℝ)).mpr (le_max_left (qabs (halfLog2PiLo - C0))
      (qabs (halfLog2PiHi - C0)))
    rwa [qabs_cast, Rat.cast_sub] at h
  have hm2 : |(halfLog2PiHi : ℝ) - C0| ≤ Mq := by
    have h := (Rat.cast_le (K := ℝ)).mpr (le_max_right (qabs (halfLog2PiLo - C0))
      (qabs (halfLog2PiHi - C0)))
    rwa [qabs_cast, Rat.cast_sub] at h
  have hgap : |(Real.log (2 * π) - 1) / 2 - C0| ≤ Mq := by
    rw [abs_le]
    have a1 := neg_abs_le ((halfLog2PiLo : ℝ) - C0)
    have a2 := le_abs_self ((halfLog2PiHi : ℝ) - C0)
    constructor <;> linarith
  have hser : |series stirCoeffs x - x⁻¹ * eval P (x⁻¹ ^ 2)| ≤ δ / 16 := by
    rw [series, ← mul_sub, abs_mul, abs_of_pos hi0]
    calc x⁻¹ * |eval stirCoeffs (x⁻¹ ^ 2) - eval P (x⁻¹ ^ 2)| ≤ 1 / 16 * δ :=
          mul_le_mul hinv he (abs_nonneg _) (by norm_num)
      _ = δ / 16 := by ring
  have hεr : (Mq : ℝ) + (δ : ℝ) / 16 + 104001 / (25 * 15 ^ 25) ≤ ε := by
    have h := (Rat.cast_le (K := ℝ)).mpr hε
    push_cast at h
    linarith
  have hsplit : lgamma x - fit C0 P x = (lgamma x - lead x - series stirCoeffs x) +
      ((Real.log (2 * π) - 1) / 2 - C0) +
      (series stirCoeffs x - x⁻¹ * eval P (x⁻¹ ^ 2)) := by
    rw [fit, lead]
    ring
  rw [hsplit]
  calc _ ≤ |lgamma x - lead x - series stirCoeffs x| + |(Real.log (2 * π) - 1) / 2 - C0| +
        |series stirCoeffs x - x⁻¹ * eval P (x⁻¹ ^ 2)| := abs_add_three _ _ _
    _ ≤ _ := by linarith

#print axioms pi_bounds20
#print axioms lgammaDiffOk_sound
#print axioms fitExpr_eval
#print axioms fit_piece
#print axioms fit_large

end LeanExe.ProofKit.GammaFits
