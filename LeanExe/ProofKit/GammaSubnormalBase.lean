import LeanExe.ProofKit.GammaReflect
import LeanExe.ProofKit.GammaConvex
import LeanExe.ProofKit.GammaFits

/-!
The lemmas of `GammaSubnormal`: the levels `tAbove` and `tBelow` of `lgamma` that give
`|Γ| ≥ 2 ^ -1022 (1 + 2 ^ -48)` and `|Γ| ≤ 2 ^ -1022 (1 - 2 ^ -48)`, the convexity of `lgamma` on
`(-n - 1, -n)` applied left and right of a crossing of a level and between two points below it, and
the point bounds of `GammaReflect.negPointOk` at the doubles `-m/2 ^ 45`.
-/

namespace LeanExe.ProofKit.GammaSubnormalBase

open Real Set TaylorModel GammaBasic GammaModels GammaFits GammaReflect GammaConvex GammaThresholds

/-- The parameters of the point models: radius 0, degree 2, 104 bits, at most 60 series terms with
factor below `2 ^ -110`, and Mathlib's 20-digit bounds on `π`. -/
def cfgS : Cfg := ⟨0, 2, 104, 60, 1 / 2 ^ 110, piLo20, piHi20⟩

theorem cfgS_pi : ((cfgS.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgS.piHi : ℚ) : ℝ) := pi_bounds20

/-- `lgamma x ≥ tAbove` gives `|Γ x| ≥ 2 ^ -1022 (1 + 2 ^ -48)` (`gamma_above`), and
`lgamma x ≤ tBelow` gives `|Γ x| ≤ 2 ^ -1022 (1 - 2 ^ -48)` (`gamma_below`). -/
def tAbove : ℚ := -1022 * log2Lo + 1 / 2 ^ 48

def tBelow : ℚ := -1022 * log2Hi - 1 / 2 ^ 48 - 2 / 2 ^ 96

theorem tBelow_lt : (tBelow : ℝ) < tAbove := by
  have h : tBelow < tAbove := by
    simp only [tBelow, tAbove, log2Lo, log2Hi]
    norm_num
  exact_mod_cast h

/-- The statement for one argument: `|Γ x|` lies `2 ^ -48` relative below or above `2 ^ -1022`. -/
def Gap (x : ℝ) : Prop :=
  |Real.Gamma x| ≤ 2 ^ (-1022 : ℤ) * (1 - 1 / 2 ^ 48) ∨
    2 ^ (-1022 : ℤ) * (1 + 1 / 2 ^ 48) ≤ |Real.Gamma x|

theorem exp_neg_1022 : Real.exp (-1022 * Real.log 2) = 2 ^ (-1022 : ℤ) := by
  rw [show -1022 * Real.log 2 = -(((1022 : ℕ) : ℝ) * Real.log 2) by push_cast; ring, Real.exp_neg,
    Real.exp_nat_mul, Real.exp_log two_pos]
  norm_num

theorem abs_gamma_eq {x : ℝ} (hx : Real.Gamma x ≠ 0) : |Real.Gamma x| = Real.exp (lgamma x) := by
  rw [lgamma, ← Real.log_abs, Real.exp_log (abs_pos.mpr hx)]

theorem gamma_above {x : ℝ} (hx : Real.Gamma x ≠ 0) (h : (tAbove : ℝ) ≤ lgamma x) :
    2 ^ (-1022 : ℤ) * (1 + 1 / 2 ^ 48) ≤ |Real.Gamma x| := by
  rw [abs_gamma_eq hx]
  have hl := log_two_lo
  have h1 : Real.exp (-1022 * Real.log 2) * Real.exp (1 / 2 ^ 48) ≤ Real.exp (lgamma x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [tAbove] at h
    push_cast at h
    linarith
  have h2 : (1 : ℝ) + 1 / 2 ^ 48 ≤ Real.exp (1 / 2 ^ 48) := by
    have := Real.add_one_le_exp (1 / 2 ^ 48 : ℝ)
    linarith
  rw [exp_neg_1022] at h1
  calc 2 ^ (-1022 : ℤ) * (1 + 1 / 2 ^ 48) ≤ 2 ^ (-1022 : ℤ) * Real.exp (1 / 2 ^ 48) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := h1

theorem gamma_below {x : ℝ} (hx : Real.Gamma x ≠ 0) (h : lgamma x ≤ (tBelow : ℝ)) :
    |Real.Gamma x| ≤ 2 ^ (-1022 : ℤ) * (1 - 1 / 2 ^ 48) := by
  rw [abs_gamma_eq hx]
  have hl := log_two_hi
  have h1 : Real.exp (lgamma x) ≤
      Real.exp (-1022 * Real.log 2) * Real.exp (-(1 / 2 ^ 48 + 2 / 2 ^ 96)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [tBelow] at h
    push_cast at h
    linarith
  have h2 : Real.exp (-(1 / 2 ^ 48 + 2 / 2 ^ 96)) ≤ 1 - 1 / 2 ^ 48 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    calc (1 - 1 / 2 ^ 48 : ℝ)⁻¹ ≤ 1 / 2 ^ 48 + 2 / 2 ^ 96 + 1 := by norm_num
      _ ≤ Real.exp (1 / 2 ^ 48 + 2 / 2 ^ 96) := Real.add_one_le_exp _
  rw [exp_neg_1022] at h1
  calc Real.exp (lgamma x) ≤ 2 ^ (-1022 : ℤ) * Real.exp (-(1 / 2 ^ 48 + 2 / 2 ^ 96)) := h1
    _ ≤ 2 ^ (-1022 : ℤ) * (1 - 1 / 2 ^ 48) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem convexOn_sub_const {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f) (T : ℝ) :
    ConvexOn ℝ s (fun y => f y - T) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : a * T + b * T = T := by rw [← add_mul, hab, one_mul]
  calc f (a * x + b * y) - T ≤ a * f x + b * f y - T := by linarith
    _ = a * (f x - T) + b * (f y - T) := by linear_combination e

/-- Left of a crossing of the level, where `lgamma` decreases: `lgamma x ≥ tAbove` for `x ≤ p1`. -/
theorem left_above (n : ℕ) {x p1 p2 : ℝ} (hx : -(n : ℝ) - 1 < x) (h1 : x ≤ p1) (h12 : p1 < p2)
    (hp2 : p2 < -n) (f1 : (tAbove : ℝ) ≤ lgamma p1) (f2 : lgamma p2 ≤ tBelow) :
    (tAbove : ℝ) ≤ lgamma x := by
  have hT := tBelow_lt
  have hf := convexOn_sub_const (convexOn_lgamma_neg n) (tAbove : ℝ)
  have h := convex_left hf ⟨hx, by linarith⟩ ⟨by linarith, hp2⟩ h1 h12
    (show (0 : ℝ) ≤ lgamma p1 - tAbove by linarith) (show lgamma p2 - (tAbove : ℝ) ≤ 0 by linarith)
  have h' : lgamma p1 - (tAbove : ℝ) ≤ lgamma x - tAbove := h
  linarith

/-- Right of a crossing of the level, where `lgamma` increases: `lgamma x ≥ tAbove` for
`x ≥ p4`. -/
theorem right_above (n : ℕ) {x p3 p4 : ℝ} (hx : x < -n) (h4 : p4 ≤ x) (h34 : p3 < p4)
    (hp3 : -(n : ℝ) - 1 < p3) (f3 : lgamma p3 ≤ tBelow) (f4 : (tAbove : ℝ) ≤ lgamma p4) :
    (tAbove : ℝ) ≤ lgamma x := by
  have hT := tBelow_lt
  have hf := convexOn_sub_const (convexOn_lgamma_neg n) (tAbove : ℝ)
  have h := convex_right hf ⟨by linarith, hx⟩ ⟨hp3, by linarith⟩ h4 h34
    (show (0 : ℝ) ≤ lgamma p4 - tAbove by linarith) (show lgamma p3 - (tAbove : ℝ) ≤ 0 by linarith)
  have h' : lgamma p4 - (tAbove : ℝ) ≤ lgamma x - tAbove := h
  linarith

/-- Between two points below the level, `lgamma` stays below it. -/
theorem mid_below (n : ℕ) {x p2 p3 : ℝ} (hp2 : -(n : ℝ) - 1 < p2) (h2 : p2 ≤ x) (h3 : x ≤ p3)
    (hp3 : p3 < -n) (f2 : lgamma p2 ≤ tBelow) (f3 : lgamma p3 ≤ tBelow) : lgamma x ≤ tBelow :=
  (convex_mid (convexOn_lgamma_neg n) ⟨hp2, by linarith⟩ ⟨by linarith, hp3⟩ h2 h3).trans
    (max_le f2 f3)

theorem neg_div_le {a b : ℕ} (h : a ≤ b) :
    -(b : ℝ) / 35184372088832 ≤ -(a : ℝ) / 35184372088832 := by
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  rw [div_le_div_iff_of_pos_right (by norm_num)]
  linarith

theorem mem_interval (n : ℕ) {m : ℕ} (h1 : n * 35184372088832 < m)
    (h2 : m < (n + 1) * 35184372088832) :
    -(n : ℝ) - 1 < -(m : ℝ) / 35184372088832 ∧ -(m : ℝ) / 35184372088832 < -n := by
  have h1' : (n : ℝ) * 35184372088832 < m := by exact_mod_cast h1
  have h2' : (m : ℝ) < (n + 1) * 35184372088832 := by exact_mod_cast h2
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

theorem gamma_ne_of_mem (n : ℕ) {x : ℝ} (h1 : -(n : ℝ) - 1 < x) (h2 : x < -n) :
    Real.Gamma x ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro k hk
  rw [hk] at h1 h2
  have a1 : (n : ℝ) < k := by linarith
  have a2 : (k : ℝ) < n + 1 := by linarith
  have b1 : n < k := by exact_mod_cast a1
  have b2 : k < n + 1 := by exact_mod_cast a2
  omega

theorem point_above (n : ℕ) (δ q : ℚ) (ds : LogData) (d : LgData) (hi : ℚ) (a : ℕ)
    (h : negPointOk cfgS n δ q ds d tAbove hi 0 = true)
    (ha : -(a : ℝ) / 35184372088832 = -(n : ℝ) - δ) :
    (tAbove : ℝ) ≤ lgamma (-(a : ℝ) / 35184372088832) := by
  rw [ha]
  exact (negPointOk_sound cfgS n δ q ds d tAbove hi 0 cfgS_pi h).1

theorem point_below (n : ℕ) (δ q : ℚ) (ds : LogData) (d : LgData) (lo : ℚ) (a : ℕ)
    (h : negPointOk cfgS n δ q ds d lo tBelow 0 = true)
    (ha : -(a : ℝ) / 35184372088832 = -(n : ℝ) - δ) :
    lgamma (-(a : ℝ) / 35184372088832) ≤ tBelow := by
  rw [ha]
  exact (negPointOk_sound cfgS n δ q ds d lo tBelow 0 cfgS_pi h).2

#print axioms tBelow_lt
#print axioms gamma_above
#print axioms gamma_below
#print axioms left_above
#print axioms right_above
#print axioms mid_below
#print axioms mem_interval
#print axioms gamma_ne_of_mem
#print axioms point_above
#print axioms point_below

end LeanExe.ProofKit.GammaSubnormalBase
