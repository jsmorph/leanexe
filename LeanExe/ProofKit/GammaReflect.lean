import LeanExe.ProofKit.TaylorCheck
import LeanExe.ProofKit.GammaModels

/-!
Kernel-checked values of `lgamma` at negative non-integer rationals, through the reflection
`lgamma x + lgamma (1 - x) = log π - log |sin (π x)|`.  For `x = -n - δ` with `0 < δ < 1`,
`lgamma x = log π - log (sin (π δ)) - lgamma (n + 1 + δ)` (`lgamma_neg_point`).  The model
`negPointExpr` writes `log (sin (π δ))` as `log q + log (1 + (sin (π δ)/q - 1))` for a rational `q`
near `sin (π δ)`, with the sine's argument reduced below `0.3 π` (`sinPiExpr`), and
`lgamma (n + 1 + δ)` with `GammaModels.lgammaExpr`, and `negPointOk` checks with
`TaylorCheck.exprOk` that it lies in `[lo, hi]` after Stirling's remainder (`negPointOk_sound`).
-/

namespace LeanExe.ProofKit.GammaReflect

open Real Finset PolyBound TaylorModel TaylorCheck GammaBasic GammaModels

/-- `log q` for a positive rational `q`, through `1/q` when `q < 1`. -/
def logQExpr (q : ℚ) (d : LogData) (l2lo l2hi : ℚ) : TaylorModel.Expr :=
  if 1 ≤ q then logExpr q d l2lo l2hi else .neg (logExpr (1 / q) d l2lo l2hi)

theorem logQExpr_eval (q : ℚ) (hq : 0 < q) (d : LogData) (l2lo l2hi : ℚ) (t : ℝ) :
    (logQExpr q d l2lo l2hi).eval t = Real.log q := by
  unfold logQExpr
  split_ifs with h
  · exact logExpr_eval q hq d l2lo l2hi t
  · simp only [TaylorModel.Expr.eval]
    rw [logExpr_eval _ (one_div_pos.mpr hq) d l2lo l2hi t]
    push_cast
    rw [one_div, Real.log_inv, neg_neg]

/-- `sin (π δ)` with an argument of at most `0.3 π` for the sine and `0.2 π` for the cosine:
`sin (π e)` or `cos (π (1/2 - e))` for `e = min (δ, 1 - δ)`. -/
def sinPiExpr (δ : ℚ) : TaylorModel.Expr :=
  let e := if δ ≤ 1 / 2 then δ else 1 - δ
  if e ≤ 3 / 10 then .sin (.mul .pi (.const e)) else .cos (.mul .pi (.const (1 / 2 - e)))

theorem sinPiExpr_eval (δ : ℚ) (t : ℝ) : (sinPiExpr δ).eval t = Real.sin (π * δ) := by
  by_cases h1 : δ ≤ 1 / 2
  · by_cases h2 : δ ≤ 3 / 10
    · simp only [sinPiExpr, h1, h2, ↓reduceIte, TaylorModel.Expr.eval]
    · simp only [sinPiExpr, h1, h2, ↓reduceIte, TaylorModel.Expr.eval]
      push_cast
      rw [show π * (1 / 2 - (δ : ℝ)) = π / 2 - π * δ by ring, Real.cos_pi_div_two_sub]
  · by_cases h2 : 1 - δ ≤ 3 / 10
    · simp only [sinPiExpr, h1, h2, ↓reduceIte, TaylorModel.Expr.eval]
      push_cast
      rw [show π * (1 - (δ : ℝ)) = π - π * δ by ring, Real.sin_pi_sub]
    · simp only [sinPiExpr, h1, h2, ↓reduceIte, TaylorModel.Expr.eval]
      push_cast
      rw [show π * (1 / 2 - (1 - (δ : ℝ))) = -(π / 2 - π * δ) by ring, Real.cos_neg,
        Real.cos_pi_div_two_sub]

/-- `log (sin (π δ))` as `log q + log (1 + (sin (π δ)/q - 1))`. -/
def logSinExpr (δ q : ℚ) (d : LogData) (l2lo l2hi : ℚ) : TaylorModel.Expr :=
  .add (logQExpr q d l2lo l2hi)
    (.log1p (.add (.mul (.const (1 / q)) (sinPiExpr δ)) (.const (-1))))

theorem logSinExpr_eval (δ q : ℚ) (hq : 0 < q) (d : LogData) (l2lo l2hi : ℚ) (t : ℝ)
    (hs : 0 < Real.sin (π * δ)) :
    (logSinExpr δ q d l2lo l2hi).eval t = Real.log (Real.sin (π * δ)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [logSinExpr, TaylorModel.Expr.eval]
  rw [logQExpr_eval q hq, sinPiExpr_eval]
  push_cast
  rw [show (1 : ℝ) + (1 / q * Real.sin (π * δ) + -1) = Real.sin (π * δ) / q by ring,
    Real.log_div hs.ne' hq'.ne']
  ring

/-- `lgamma (-n - δ) = log π - log (sin (π δ)) - lgamma (n + 1 + δ)` for `0 < δ < 1`. -/
theorem lgamma_neg_point (n : ℕ) {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    lgamma (-n - δ) = Real.log π - Real.log (Real.sin (π * δ)) - lgamma (n + 1 + δ) := by
  have hni : ∀ m : ℤ, (-(n : ℝ) - δ) ≠ m := by
    intro m hm
    have he : δ = ((-(n : ℤ) - m : ℤ) : ℝ) := by
      push_cast
      linarith
    rw [he] at h0 h1
    have h0' : (0 : ℤ) < -(n : ℤ) - m := by exact_mod_cast h0
    have h1' : -(n : ℤ) - m < 1 := by exact_mod_cast h1
    omega
  have hr := lgamma_reflect hni
  have hspos : 0 < Real.sin (π * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hs : Real.sin (π * (-(n : ℝ) - δ)) = -((-1) ^ n * Real.sin (π * δ)) := by
    rw [show π * (-(n : ℝ) - δ) = -(π * δ + n * π) by ring, Real.sin_neg,
      Real.sin_add_nat_mul_pi]
  have hl : Real.log (Real.sin (π * (-(n : ℝ) - δ))) = Real.log (Real.sin (π * δ)) := by
    rw [← Real.log_abs, hs, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hspos]
  rw [hl, show (1 : ℝ) - (-(n : ℝ) - δ) = n + 1 + δ by ring] at hr
  linarith

/-- The model of `lgamma (-n - δ)` with `d` a model of `lgamma` at `n + 1 + δ`. -/
def negPointExpr (δ q : ℚ) (ds : LogData) (d : LgData) : TaylorModel.Expr :=
  Expr.sub (Expr.sub (logPiExpr d.l2lo d.l2hi) (logSinExpr δ q ds d.l2lo d.l2hi)) (lgammaExpr d)

/-- The kernel check that `lo ≤ lgamma (-n - δ) ≤ hi`. -/
def negPointOk (c : Cfg) (n : ℕ) (δ q : ℚ) (ds : LogData) (d : LgData) (lo hi : ℚ)
    (depth : ℕ) : Bool :=
  decide (0 < δ) && decide (δ < 1) && decide (0 < q) && decide (d.a = n + 1 + δ) &&
    decide (16 ≤ d.a + d.n) && decide (0 ≤ c.r) &&
    exprOk c (.add (negPointExpr δ q ds d) (.const (-((lo + hi) / 2))))
      ((hi - lo) / 2 - stirRemQ d 0) depth

theorem negPointOk_sound (c : Cfg) (n : ℕ) (δ q : ℚ) (ds : LogData) (d : LgData) (lo hi : ℚ)
    (depth : ℕ) (hpi : (c.piLo : ℝ) ≤ π ∧ π ≤ c.piHi)
    (h : negPointOk c n δ q ds d lo hi depth = true) :
    (lo : ℝ) ≤ lgamma (-n - δ) ∧ lgamma (-n - δ) ≤ hi := by
  simp only [negPointOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hδ0, hδ1⟩, hq⟩, hda⟩, hY⟩, hr⟩, hm⟩ := h
  have hδ0r : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1r : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hspos : 0 < Real.sin (π * δ) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have ha : (0 : ℚ) < d.a := by
    rw [hda]
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  have he := exprOk_sound c _ _ depth hpi hm (t := 0) (by rw [abs_zero]; exact_mod_cast hr)
  have hs := lgamma_sub_expr_le d (r := 0) le_rfl ha (by linarith) (t := 0) (by simp)
  rw [stirRem_eq] at hs
  simp only [negPointExpr, Expr.sub, TaylorModel.Expr.eval] at he
  rw [logPiExpr_eval, logSinExpr_eval δ q hq ds d.l2lo d.l2hi 0 hspos] at he
  have hp := lgamma_neg_point n hδ0r hδ1r
  have hda' : ((d.a : ℚ) : ℝ) + 0 = n + 1 + δ := by
    rw [add_zero, hda]
    norm_num
  rw [hda'] at hs
  push_cast at he hs
  rw [abs_le] at he hs
  constructor <;> linarith [he.1, he.2, hs.1, hs.2]

#print axioms lgamma_neg_point
#print axioms negPointOk_sound

end LeanExe.ProofKit.GammaReflect
