import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Izzo's time of flight for Lambert's problem with zero revolutions, and its representation by an
integral.  For `-1 < λ < 1` (written `lam`) and `x > -1`, `tof lam x` is Izzo's equation (18):
`(ψ/√(1 - x²) - x + λ y)/(1 - x²)` with `ψ = arccos(x y + λ(1 - x²))` below 1,
`(2/3)(1 - λ³)` at 1, and `(ψ/√(x² - 1) - x + λ y)/(1 - x²)` with
`ψ = arcosh(x y - λ(x² - 1))` above 1, where `y = √(1 - λ²(1 - x²))`.

`tof_pos_eq` writes `tof lam x` for `x > 0` as `2 ∫ from λ to 1 of σ²/√(1 - (1 - x²) σ²)`, and
`tof_neg_eq` writes it for `-1 < x < 0` as `π/(1 - x²)^(3/2)` less the same integral from `-λ`
to 1.  The integrand increases with `1 - x²` at every `σ ≠ 0`, which `LambertRoot.lean` uses for
the monotonicity of `tof`.
-/

namespace Demos.Orbit.Lambert

open Real Set intervalIntegral

/-- `y = √(1 - λ²(1 - x²))`. -/
noncomputable def yOf (lam x : ℝ) : ℝ := √(1 - lam ^ 2 * (1 - x ^ 2))

/-- Izzo's time of flight for zero revolutions. -/
noncomputable def tof (lam x : ℝ) : ℝ :=
  if x < 1 then
    (arccos (x * yOf lam x + lam * (1 - x ^ 2)) / √(1 - x ^ 2) - x + lam * yOf lam x) /
      (1 - x ^ 2)
  else if x = 1 then 2 / 3 * (1 - lam ^ 3)
  else
    (arcosh (x * yOf lam x - lam * (x ^ 2 - 1)) / √(x ^ 2 - 1) - x + lam * yOf lam x) /
      (1 - x ^ 2)

/-- The integrand `σ²/√(1 - w σ²)`. -/
noncomputable def integrand (w s : ℝ) : ℝ := s ^ 2 / √(1 - w * s ^ 2)

/-! ### The two forms of `ψ` -/

theorem yOf_sq {lam x : ℝ} (h : 0 ≤ 1 - lam ^ 2 * (1 - x ^ 2)) :
    yOf lam x ^ 2 = 1 - lam ^ 2 * (1 - x ^ 2) := sq_sqrt h

/-- Below 1, `ψ` is the difference of the angles `arccos x` and `arcsin(λ √(1 - x²))`. -/
theorem psi_elliptic {lam x : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hx0 : -1 < x) (hx1 : x < 1) :
    arccos (x * yOf lam x + lam * (1 - x ^ 2)) = arccos x - arcsin (lam * √(1 - x ^ 2)) := by
  set A := arccos x
  set s := √(1 - x ^ 2) with hs
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - x ^ 2 := sq_sqrt (by nlinarith)
  have hs1 : s ≤ 1 := by nlinarith
  have hls : -1 ≤ lam * s ∧ lam * s ≤ 1 := by constructor <;> nlinarith
  set B := arcsin (lam * s)
  have hsinA : sin A = s := sin_arccos x
  have hcosA : cos A = x := cos_arccos hx0.le hx1.le
  have hsinB : sin B = lam * s := sin_arcsin hls.1 hls.2
  have hcosB : cos B = yOf lam x := by
    rw [cos_arcsin, yOf]; congr 1; rw [mul_pow, hs2]
  have hc : cos (A - B) = x * yOf lam x + lam * (1 - x ^ 2) := by
    rw [cos_sub, hsinA, hcosA, hsinB, hcosB, ← hs2]; ring
  rw [← hc]
  have hA0 := arccos_nonneg x
  have hAπ := arccos_le_pi x
  have hB1 := arcsin_le_pi_div_two (lam * s)
  have hB0 := neg_pi_div_two_le_arcsin (lam * s)
  apply arccos_cos
  · -- `B ≤ A`
    by_cases h : A ≤ π / 2
    · have : B ≤ arcsin s := arcsin_le_arcsin (by nlinarith)
      have e : arcsin s = A := by rw [← hsinA]; exact arcsin_sin (by linarith) h
      linarith
    · linarith
  · -- `A - π ≤ B`
    by_cases h : π / 2 ≤ A
    · have : arcsin (-s) ≤ B := arcsin_le_arcsin (by nlinarith)
      have e : arcsin (-s) = A - π := by
        rw [← hsinA, ← sin_sub_pi]; exact arcsin_sin (by linarith) (by linarith)
      linarith
    · linarith

/-- Above 1, `ψ` is the difference `arsinh √(x² - 1) - arsinh(λ √(x² - 1))`. -/
theorem psi_hyperbolic {lam x : ℝ} (hl1 : lam < 1) (hx1 : 1 < x) :
    arcosh (x * yOf lam x - lam * (x ^ 2 - 1)) =
      arsinh √(x ^ 2 - 1) - arsinh (lam * √(x ^ 2 - 1)) := by
  set k := √(x ^ 2 - 1)
  have hk0 : 0 ≤ k := sqrt_nonneg _
  have hk2 : k ^ 2 = x ^ 2 - 1 := sq_sqrt (by nlinarith)
  have hca : cosh (arsinh k) = x := by
    rw [cosh_arsinh, hk2]; ring_nf; exact sqrt_sq (by linarith)
  have hcb : cosh (arsinh (lam * k)) = yOf lam x := by
    rw [cosh_arsinh, yOf]; congr 1; rw [mul_pow, hk2]; ring
  have hc : cosh (arsinh k - arsinh (lam * k)) = x * yOf lam x - lam * (x ^ 2 - 1) := by
    rw [cosh_sub, hca, hcb, sinh_arsinh, sinh_arsinh, ← hk2]; ring
  rw [← hc]
  apply arcosh_cosh
  have : arsinh (lam * k) ≤ arsinh k := arsinh_le_arsinh.mpr (by nlinarith)
  linarith

/-! ### Antiderivatives of the integrand -/

/-- An antiderivative of `σ²/√(1 - w σ²)` for `w > 0`. -/
noncomputable def primE (w s : ℝ) : ℝ := (arcsin (√w * s) / √w - s * √(1 - w * s ^ 2)) / (2 * w)

/-- An antiderivative of `σ²/√(1 + v σ²)` for `v > 0`. -/
noncomputable def primH (v s : ℝ) : ℝ := (s * √(1 + v * s ^ 2) - arsinh (√v * s) / √v) / (2 * v)

theorem hasDerivAt_primE {w s : ℝ} (hw : 0 < w) (hs : w * s ^ 2 < 1) :
    HasDerivAt (primE w) (integrand w s) s := by
  have hq : 0 < 1 - w * s ^ 2 := by linarith
  have hrw : 0 < √w := sqrt_pos.mpr hw
  have hw2 : √w ^ 2 = w := sq_sqrt hw.le
  have harg : (√w * s) ^ 2 < 1 := by rw [mul_pow, hw2]; exact hs
  have h1 : √w * s ≠ -1 := by intro h; rw [h] at harg; norm_num at harg
  have h2 : √w * s ≠ 1 := by intro h; rw [h] at harg; norm_num at harg
  have dlin : HasDerivAt (fun t => √w * t) (√w) s := by
    simpa using (hasDerivAt_id s).const_mul (√w)
  have das := (hasDerivAt_arcsin h1 h2).comp s dlin
  have dq : HasDerivAt (fun t => 1 - w * t ^ 2) (-(w * (2 * s))) s := by
    simpa using ((hasDerivAt_pow 2 s).const_mul w).const_sub 1
  have dsq := dq.sqrt hq.ne'
  have dprod := (hasDerivAt_id s).fun_mul dsq
  have := ((das.div_const (√w)).fun_sub dprod).div_const (2 * w)
  refine this.congr_deriv ?_
  have e1 : 1 - (√w * s) ^ 2 = 1 - w * s ^ 2 := by rw [mul_pow, hw2]
  rw [e1, integrand]
  have hsq := sq_sqrt hq.le
  have hsq0 : 0 < √(1 - w * s ^ 2) := sqrt_pos.mpr hq
  simp only [id]
  field_simp
  linear_combination -hsq

theorem hasDerivAt_primH {v s : ℝ} (hv : 0 < v) :
    HasDerivAt (primH v) (integrand (-v) s) s := by
  have hq : 0 < 1 + v * s ^ 2 := by positivity
  have hrv : 0 < √v := sqrt_pos.mpr hv
  have hv2 : √v ^ 2 = v := sq_sqrt hv.le
  have dlin : HasDerivAt (fun t => √v * t) (√v) s := by
    simpa using (hasDerivAt_id s).const_mul (√v)
  have das := dlin.arsinh
  have dq : HasDerivAt (fun t => 1 + v * t ^ 2) (v * (2 * s)) s := by
    simpa using ((hasDerivAt_pow 2 s).const_mul v).const_add 1
  have dsq := dq.sqrt hq.ne'
  have dprod := (hasDerivAt_id s).fun_mul dsq
  have := (dprod.fun_sub (das.div_const (√v))).div_const (2 * v)
  refine this.congr_deriv ?_
  have e1 : 1 + (√v * s) ^ 2 = 1 + v * s ^ 2 := by rw [mul_pow, hv2]
  rw [e1, integrand, show 1 - -v * s ^ 2 = 1 + v * s ^ 2 by ring]
  have hsq := sq_sqrt hq.le
  have hsq0 : 0 < √(1 + v * s ^ 2) := sqrt_pos.mpr hq
  simp only [id, smul_eq_mul]
  field_simp
  linear_combination hsq

/-! ### The integral representations -/

theorem continuousOn_integrand {w a b : ℝ} (h : ∀ s ∈ uIcc a b, 0 < 1 - w * s ^ 2) :
    ContinuousOn (integrand w) (uIcc a b) := by
  unfold integrand
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro s hs
  exact (sqrt_pos.mpr (h s hs)).ne'

theorem integrand_pos_den {w a b : ℝ} (hw : w < 1) (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    ∀ s ∈ uIcc a b, 0 < 1 - w * s ^ 2 := by
  intro s hs
  rw [uIcc_of_le hab] at hs
  have h1 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  rcases le_total 0 w with h | h
  · nlinarith
  · nlinarith [sq_nonneg s]

theorem integral_elliptic {w a b : ℝ} (hw : 0 < w) (hw1 : w < 1) (ha : -1 ≤ a) (hb : b ≤ 1)
    (hab : a ≤ b) : ∫ s in a..b, integrand w s = primE w b - primE w a := by
  have hd := integrand_pos_den hw1 ha hb hab
  apply integral_eq_sub_of_hasDerivAt
  · intro s hs
    exact hasDerivAt_primE hw (by linarith [hd s hs])
  · exact (continuousOn_integrand hd).intervalIntegrable

theorem integral_hyperbolic {v a b : ℝ} (hv : 0 < v) (ha : -1 ≤ a) (hb : b ≤ 1)
    (hab : a ≤ b) : ∫ s in a..b, integrand (-v) s = primH v b - primH v a := by
  have hd := integrand_pos_den (w := -v) (by linarith) ha hb hab
  apply integral_eq_sub_of_hasDerivAt
  · intro s _
    exact hasDerivAt_primH hv
  · exact (continuousOn_integrand hd).intervalIntegrable

/-- For `x > 0`, `tof lam x = 2 ∫ from λ to 1 of σ²/√(1 - (1 - x²) σ²)`. -/
theorem tof_pos_eq {lam x : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hx : 0 < x) :
    tof lam x = 2 * ∫ s in lam..1, integrand (1 - x ^ 2) s := by
  have hy : yOf lam x ^ 2 = 1 - lam ^ 2 * (1 - x ^ 2) := by
    apply yOf_sq
    rcases le_total x 1 with h | h <;> nlinarith
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · have hw : 0 < 1 - x ^ 2 := by nlinarith
    rw [integral_elliptic hw (by nlinarith) hl0.le le_rfl hl1.le]
    simp only [tof, h1, ite_true]
    rw [psi_elliptic hl0 hl1 (by linarith) h1, arccos_eq_arcsin hx.le]
    simp only [primE]
    have e1 : √(1 - (1 - x ^ 2) * 1 ^ 2) = x := by
      rw [show 1 - (1 - x ^ 2) * 1 ^ 2 = x ^ 2 by ring]; exact sqrt_sq hx.le
    have e2 : √(1 - (1 - x ^ 2) * lam ^ 2) = yOf lam x := by
      rw [yOf]; congr 1; ring
    rw [e1, e2, mul_one, mul_comm (√(1 - x ^ 2)) lam]
    have hr : 0 < √(1 - x ^ 2) := sqrt_pos.mpr hw
    field_simp
    ring
  · subst h1
    simp only [tof, lt_irrefl, ite_false, ite_true]
    have e : (fun s => integrand (1 - 1 ^ 2) s) = fun s => s ^ 2 := by
      funext s; simp [integrand]
    rw [e, integral_pow]
    ring
  · have hv : 0 < x ^ 2 - 1 := by nlinarith
    have hw : 1 - x ^ 2 = -(x ^ 2 - 1) := by ring
    rw [hw, integral_hyperbolic hv hl0.le le_rfl hl1.le]
    simp only [tof, not_lt.mpr h1.le, h1.ne', ite_false]
    rw [psi_hyperbolic hl1 h1]
    simp only [primH]
    have e1 : √(1 + (x ^ 2 - 1) * 1 ^ 2) = x := by
      rw [show 1 + (x ^ 2 - 1) * 1 ^ 2 = x ^ 2 by ring]; exact sqrt_sq hx.le
    have e2 : √(1 + (x ^ 2 - 1) * lam ^ 2) = yOf lam x := by
      rw [yOf]; congr 1; ring
    rw [e1, e2, mul_one, mul_comm (√(x ^ 2 - 1)) lam]
    have hr : 0 < √(x ^ 2 - 1) := sqrt_pos.mpr hv
    have hv' : 1 - x ^ 2 ≠ 0 := by linarith
    field_simp
    ring

/-- For `-1 < x < 0`, `tof lam x = π/(1 - x²)^(3/2) - 2 ∫ from -λ to 1 of
σ²/√(1 - (1 - x²) σ²)`. -/
theorem tof_neg_eq {lam x : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hx0 : -1 < x) (hx : x < 0) :
    tof lam x = π / ((1 - x ^ 2) * √(1 - x ^ 2)) -
      2 * ∫ s in (-lam)..1, integrand (1 - x ^ 2) s := by
  have hw : 0 < 1 - x ^ 2 := by nlinarith
  rw [integral_elliptic hw (by nlinarith) (by linarith) le_rfl (by linarith)]
  simp only [tof, show x < 1 by linarith, ite_true]
  rw [psi_elliptic hl0 hl1 hx0 (by linarith)]
  simp only [primE]
  have e0 : arcsin √(1 - x ^ 2) = π - arccos x := by
    rw [← arccos_neg, arccos_eq_arcsin (by linarith), neg_sq]
  have e1 : √(1 - (1 - x ^ 2) * 1 ^ 2) = -x := by
    rw [show 1 - (1 - x ^ 2) * 1 ^ 2 = (-x) ^ 2 by ring]; exact sqrt_sq (by linarith)
  have e2 : √(1 - (1 - x ^ 2) * (-lam) ^ 2) = yOf lam x := by
    rw [yOf]; congr 1; ring
  rw [mul_one, e0, e1, e2]
  simp only [mul_neg, neg_mul, one_mul, arcsin_neg]
  rw [mul_comm (√(1 - x ^ 2)) lam]
  have hr : 0 < √(1 - x ^ 2) := sqrt_pos.mpr hw
  field_simp
  ring

end Demos.Orbit.Lambert
