import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Logic.Function.Basic

/-!
Kepler's equation in the form of SGP4, `E + b cos E - a sin E = u`.  For `a² + b² < 1` the left
side increases with slope at least `1 - √(a² + b²)`, so the equation has exactly one root
(`exists_unique_root`), and every `E` lies within `|lhs a b E - u| / (1 - √(a² + b²))` of the
root (`root_bound`).
-/

namespace Demos.Sgp4.Kepler

open Real Filter

/-- The left side of Kepler's equation. -/
noncomputable def lhs (a b E : ℝ) : ℝ := E + b * cos E - a * sin E

theorem combination_le (a b m : ℝ) : |b * sin m + a * cos m| ≤ √(a ^ 2 + b ^ 2) := by
  apply abs_le_sqrt
  have h := sin_sq_add_cos_sq m
  have e : (b * sin m + a * cos m) ^ 2 =
      (a ^ 2 + b ^ 2) * (sin m ^ 2 + cos m ^ 2) - (b * cos m - a * sin m) ^ 2 := by ring
  rw [e, h]
  nlinarith [sq_nonneg (b * cos m - a * sin m)]

/-- The left side rises by at least `1 - √(a² + b²)` times the distance. -/
theorem growth (a b : ℝ) {E₁ E₂ : ℝ} (h : E₁ ≤ E₂) :
    (1 - √(a ^ 2 + b ^ 2)) * (E₂ - E₁) ≤ lhs a b E₂ - lhs a b E₁ := by
  have e : lhs a b E₂ - lhs a b E₁ = (E₂ - E₁) -
      2 * (sin ((E₂ - E₁) / 2) * (b * sin ((E₂ + E₁) / 2) + a * cos ((E₂ + E₁) / 2))) := by
    unfold lhs
    linear_combination b * cos_sub_cos E₂ E₁ - a * sin_sub_sin E₂ E₁
  have hs : |sin ((E₂ - E₁) / 2)| ≤ (E₂ - E₁) / 2 := by
    have := abs_sin_le_abs (x := (E₂ - E₁) / 2)
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (E₂ - E₁) / 2)] at this
  have hc := combination_le a b ((E₂ + E₁) / 2)
  have hp : sin ((E₂ - E₁) / 2) * (b * sin ((E₂ + E₁) / 2) + a * cos ((E₂ + E₁) / 2)) ≤
      (E₂ - E₁) / 2 * √(a ^ 2 + b ^ 2) :=
    calc _ ≤ |sin ((E₂ - E₁) / 2) * (b * sin ((E₂ + E₁) / 2) + a * cos ((E₂ + E₁) / 2))| :=
          le_abs_self _
      _ = |sin ((E₂ - E₁) / 2)| * |b * sin ((E₂ + E₁) / 2) + a * cos ((E₂ + E₁) / 2)| :=
          abs_mul _ _
      _ ≤ _ := mul_le_mul hs hc (abs_nonneg _) (by linarith)
  rw [e]
  nlinarith [hp]

theorem slope_pos {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) : 0 < 1 - √(a ^ 2 + b ^ 2) := by
  have := (sqrt_lt_sqrt (by positivity) h).trans_eq sqrt_one
  linarith

theorem lhs_strictMono {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) : StrictMono (lhs a b) := by
  intro E₁ E₂ hlt
  have g := growth a b hlt.le
  have : 0 < (1 - √(a ^ 2 + b ^ 2)) * (E₂ - E₁) := mul_pos (slope_pos h) (sub_pos.2 hlt)
  linarith

theorem lhs_near {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) (E : ℝ) :
    E - 2 ≤ lhs a b E ∧ lhs a b E ≤ E + 2 := by
  have ha : |a| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg b]
  have hb : |b| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg a]
  have h1 : |b * cos E| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ hb (abs_nonneg _) (abs_cos_le_one E)
  have h2 : |a * sin E| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) (abs_sin_le_one E)
  rw [abs_le] at h1 h2
  unfold lhs
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem lhs_surjective {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) : Function.Surjective (lhs a b) := by
  have hc : Continuous (lhs a b) := by unfold lhs; fun_prop
  refine hc.surjective ?_ ?_
  · exact tendsto_atTop_mono (fun E => (lhs_near h E).1)
      (tendsto_atTop_add_const_right atTop (-2) tendsto_id)
  · exact tendsto_atBot_mono (fun E => (lhs_near h E).2)
      (tendsto_atBot_add_const_right atBot 2 tendsto_id)

/-- **S1.**  For `a² + b² < 1`, Kepler's equation has exactly one root. -/
theorem exists_unique_root {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) (u : ℝ) :
    ∃! E, lhs a b E = u := by
  obtain ⟨E, hE⟩ := lhs_surjective h u
  exact ⟨E, hE, fun y hy => (lhs_strictMono h).injective (hy.trans hE.symm)⟩

/-- The root of Kepler's equation when `a² + b² < 1`. -/
noncomputable def root (a b u : ℝ) : ℝ := Function.invFun (lhs a b) u

theorem root_spec {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) (u : ℝ) : lhs a b (root a b u) = u :=
  Function.invFun_eq (lhs_surjective h u)

/-- The distance of `E` from the root is at most the residual over the least slope. -/
theorem root_bound {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) (u E : ℝ) :
    |E - root a b u| ≤ |lhs a b E - u| / (1 - √(a ^ 2 + b ^ 2)) := by
  have hr := root_spec h u
  rw [le_div_iff₀ (slope_pos h)]
  rcases le_total (root a b u) E with hle | hle
  · have g := growth a b hle
    rw [abs_of_nonneg (sub_nonneg.2 hle)]
    have := le_abs_self (lhs a b E - u)
    nlinarith
  · have g := growth a b hle
    rw [abs_of_nonpos (sub_nonpos.2 hle)]
    have := neg_abs_le (lhs a b E - u)
    nlinarith

end Demos.Sgp4.Kepler
