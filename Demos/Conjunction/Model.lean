import LeanExe.ProofKit.RealErf
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
The two-dimensional probability of collision.  `pc` is the integral of a Gaussian density with
mean `(m1, m2)` and covariance `[[c11, c12], [c12, c22]]` over the disk of radius `r` about the
origin.  `pc_eq` writes it as an integral over the first coordinate of `core`, the product of an
exponential and a sum of two error-function values, and `integral_eq_width_mul` bounds the
integral of a function over an interval by its bounds there.
-/

namespace Demos.Conjunction.Model

open Real MeasureTheory Set LeanExe.ProofKit

/-- The determinant of the covariance. -/
def det (c11 c12 c22 : ℝ) : ℝ := c11 * c22 - c12 ^ 2

/-- The Gaussian density of the miss vector at the point `p` of the encounter plane. -/
noncomputable def density (m1 m2 c11 c12 c22 : ℝ) (p : ℝ × ℝ) : ℝ :=
  (2 * π * √(det c11 c12 c22))⁻¹ *
    exp (-(c22 * (p.1 - m1) ^ 2 - 2 * c12 * (p.1 - m1) * (p.2 - m2) + c11 * (p.2 - m2) ^ 2) /
      (2 * det c11 c12 c22))

/-- The disk of radius `r` about the origin. -/
def disk (r : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2}

/-- The probability that the miss vector lies in the disk of radius `r`. -/
noncomputable def pc (m1 m2 c11 c12 c22 r : ℝ) : ℝ :=
  ∫ p in disk r, density m1 m2 c11 c12 c22 p

/-- The variance of the second coordinate given the first. -/
noncomputable def condVar (c11 c12 c22 : ℝ) : ℝ := c22 - c12 ^ 2 / c11

/-- The mean of the second coordinate given that the first is `x`. -/
noncomputable def condMean (m1 m2 c11 c12 x : ℝ) : ℝ := m2 + c12 / c11 * (x - m1)

/-- The conditional standard deviation times `√2`, the scale of the error-function arguments. -/
noncomputable def scaleK (c11 c12 c22 : ℝ) : ℝ := √(condVar c11 c12 c22) * √2

/-- The integrand over the first coordinate, without its constant factor. -/
noncomputable def core (m1 m2 c11 c12 c22 r x : ℝ) : ℝ :=
  exp (-(x - m1) ^ 2 / (2 * c11)) *
    (RealErf.erf ((√(r ^ 2 - x ^ 2) - condMean m1 m2 c11 c12 x) / scaleK c11 c12 c22) +
      RealErf.erf ((√(r ^ 2 - x ^ 2) + condMean m1 m2 c11 c12 x) / scaleK c11 c12 c22))

theorem continuous_erf : Continuous RealErf.erf :=
  continuous_iff_continuousAt.mpr fun x => (RealErf.hasDerivAt_erf x).continuousAt

theorem continuous_core (m1 m2 c11 c12 c22 r : ℝ) : Continuous (core m1 m2 c11 c12 c22 r) := by
  unfold core condMean
  exact Continuous.mul (by fun_prop)
    (Continuous.add (continuous_erf.comp (by fun_prop)) (continuous_erf.comp (by fun_prop)))

theorem continuous_density (m1 m2 c11 c12 c22 : ℝ) : Continuous (density m1 m2 c11 c12 c22) := by
  unfold density
  fun_prop

/-- The integral of a Gaussian window as a difference of error-function values. -/
theorem gauss_window (μ v a b : ℝ) (hv : 0 < v) :
    ∫ y in a..b, exp (-(y - μ) ^ 2 / (2 * v)) =
      √(2 * π * v) *
        (1 / 2 * (RealErf.erf ((b - μ) / (√v * √2)) - RealErf.erf ((a - μ) / (√v * √2)))) := by
  have hk0 : 0 < √v * √2 := mul_pos (Real.sqrt_pos.mpr hv) (Real.sqrt_pos.mpr two_pos)
  have hk2 : (√v * √2) ^ 2 = 2 * v := by
    rw [mul_pow, Real.sq_sqrt hv.le, Real.sq_sqrt zero_le_two]
    ring
  have e : (fun y : ℝ => exp (-(y - μ) ^ 2 / (2 * v))) =
      fun y => exp (-(y / (√v * √2) - μ / (√v * √2)) ^ 2) := by
    funext y
    have h1 : y / (√v * √2) - μ / (√v * √2) = (y - μ) / (√v * √2) := by ring
    rw [h1, div_pow, hk2, neg_div]
  have hc := intervalIntegral.integral_comp_div_sub (a := a) (b := b)
    (fun t : ℝ => exp (-t ^ 2)) hk0.ne' (μ / (√v * √2))
  have hint : ∀ c d : ℝ, IntervalIntegrable (fun t : ℝ => exp (-t ^ 2)) volume c d :=
    fun c d => RealErf.continuous_gauss.intervalIntegrable c d
  have hsub := intervalIntegral.integral_interval_sub_left (hint 0 ((b - μ) / (√v * √2)))
    (hint 0 ((a - μ) / (√v * √2)))
  have ha : a / (√v * √2) - μ / (√v * √2) = (a - μ) / (√v * √2) := by ring
  have hb : b / (√v * √2) - μ / (√v * √2) = (b - μ) / (√v * √2) := by ring
  have hs : √(2 * π * v) = √v * √2 * √π := by
    rw [show 2 * π * v = v * 2 * π by ring, Real.sqrt_mul (mul_nonneg hv.le zero_le_two),
      Real.sqrt_mul hv.le]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  rw [e, hc, ha, hb, ← hsub, smul_eq_mul, hs]
  unfold RealErf.erf RealErf.scale
  field_simp

/-- The density as the marginal density of the first coordinate times the conditional density
of the second. -/
theorem density_factor (m1 m2 c11 c12 c22 : ℝ) (hc : 0 < c11) (hd : 0 < det c11 c12 c22)
    (x y : ℝ) :
    density m1 m2 c11 c12 c22 (x, y) =
      (√(2 * π * c11))⁻¹ * exp (-(x - m1) ^ 2 / (2 * c11)) *
        ((√(2 * π * condVar c11 c12 c22))⁻¹ *
          exp (-(y - condMean m1 m2 c11 c12 x) ^ 2 / (2 * condVar c11 c12 c22))) := by
  have hv : condVar c11 c12 c22 = det c11 c12 c22 / c11 := by
    unfold condVar det
    field_simp
  have hp : √(2 * π * c11) * √(2 * π * condVar c11 c12 c22) = 2 * π * √(det c11 c12 c22) := by
    rw [← Real.sqrt_mul (mul_pos (mul_pos two_pos pi_pos) hc).le,
      show 2 * π * c11 * (2 * π * condVar c11 c12 c22) = (2 * π) ^ 2 * det c11 c12 c22 by
        rw [hv]; field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_pos two_pos pi_pos).le]
  have hE : -(c22 * (x - m1) ^ 2 - 2 * c12 * (x - m1) * (y - m2) + c11 * (y - m2) ^ 2) /
        (2 * det c11 c12 c22) =
      -(x - m1) ^ 2 / (2 * c11) +
        -(y - condMean m1 m2 c11 c12 x) ^ 2 / (2 * condVar c11 c12 c22) := by
    rw [hv]
    unfold condMean
    have hc' := hc.ne'
    have hd' : det c11 c12 c22 ≠ 0 := hd.ne'
    have h22 : c22 = (det c11 c12 c22 + c12 ^ 2) / c11 := by
      rw [eq_div_iff hc']
      unfold det
      ring
    generalize det c11 c12 c22 = d at hd' h22 ⊢
    subst h22
    field_simp
    ring
  show (2 * π * √(det c11 c12 c22))⁻¹ * exp (-(c22 * (x - m1) ^ 2 -
    2 * c12 * (x - m1) * (y - m2) + c11 * (y - m2) ^ 2) / (2 * det c11 c12 c22)) = _
  rw [hE, Real.exp_add, ← hp, mul_inv]
  ring

/-- The integral of a continuous function over the disk as an iterated integral. -/
theorem disk_integral (f : ℝ × ℝ → ℝ) (hf : Continuous f) (r : ℝ) (hr : 0 ≤ r) :
    ∫ p in disk r, f p =
      ∫ x in (-r)..r, ∫ y in (-√(r ^ 2 - x ^ 2))..√(r ^ 2 - x ^ 2), f (x, y) := by
  have hclosed : IsClosed (disk r) :=
    isClosed_le (f := fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (g := fun _ => r ^ 2) (by fun_prop)
      continuous_const
  have hmeas : MeasurableSet (disk r) := hclosed.measurableSet
  have hsub : disk r ⊆ Icc (-r) r ×ˢ Icc (-r) r := by
    intro p hp
    have hp' : p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2 := hp
    exact ⟨abs_le.mp (abs_le_of_sq_le_sq (by nlinarith [sq_nonneg p.2]) hr),
      abs_le.mp (abs_le_of_sq_le_sq (by nlinarith [sq_nonneg p.1]) hr)⟩
  have hcomp : IsCompact (disk r) :=
    IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) hclosed hsub
  have hint : IntegrableOn f (disk r) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact hcomp
  have houter : ∀ x, x ∉ Icc (-r) r → ∫ y, (disk r).indicator f (x, y) = 0 := by
    intro x hx
    have hz : ∀ y, (disk r).indicator f (x, y) = 0 := by
      intro y
      refine Set.indicator_of_notMem (fun hmem => hx ?_) f
      have hp' : x ^ 2 + y ^ 2 ≤ r ^ 2 := hmem
      exact abs_le.mp (abs_le_of_sq_le_sq (by nlinarith [sq_nonneg y]) hr)
    simp [hz]
  have hinner : ∀ x ∈ Icc (-r) r, ∫ y, (disk r).indicator f (x, y) =
      ∫ y in (-√(r ^ 2 - x ^ 2))..√(r ^ 2 - x ^ 2), f (x, y) := by
    intro x hx
    have hx2 : 0 ≤ r ^ 2 - x ^ 2 := sub_nonneg.mpr (sq_le_sq' hx.1 hx.2)
    have hfun : (fun y => (disk r).indicator f (x, y)) =
        (Icc (-√(r ^ 2 - x ^ 2)) √(r ^ 2 - x ^ 2)).indicator fun y => f (x, y) := by
      funext y
      by_cases hy : y ∈ Icc (-√(r ^ 2 - x ^ 2)) √(r ^ 2 - x ^ 2)
      · have hm : (x, y) ∈ disk r := by
          have := (Real.sq_le hx2).mpr hy
          show x ^ 2 + y ^ 2 ≤ r ^ 2
          linarith
        rw [Set.indicator_of_mem hm, Set.indicator_of_mem hy]
      · have hm : (x, y) ∉ disk r := by
          intro hmem
          have hp' : x ^ 2 + y ^ 2 ≤ r ^ 2 := hmem
          exact hy ((Real.sq_le hx2).mp (by linarith))
        rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hy]
    rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (neg_le_self (Real.sqrt_nonneg _))]
  rw [Measure.volume_eq_prod, ← integral_indicator hmeas,
    integral_prod _ ((integrable_indicator_iff hmeas).mpr hint),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero houter,
    setIntegral_congr_fun measurableSet_Icc hinner, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (neg_le_self hr)]

/-- The probability of collision as an integral over the first coordinate. -/
theorem pc_eq (m1 m2 c11 c12 c22 r : ℝ) (hc : 0 < c11) (hd : 0 < det c11 c12 c22)
    (hr : 0 ≤ r) :
    pc m1 m2 c11 c12 c22 r =
      (2 * √(2 * π * c11))⁻¹ * ∫ x in (-r)..r, core m1 m2 c11 c12 c22 r x := by
  have hv : 0 < condVar c11 c12 c22 := by
    have h : condVar c11 c12 c22 = det c11 c12 c22 / c11 := by
      unfold condVar det
      field_simp
    rw [h]
    exact div_pos hd hc
  have key : ∀ x : ℝ, ∫ y in (-√(r ^ 2 - x ^ 2))..√(r ^ 2 - x ^ 2),
      density m1 m2 c11 c12 c22 (x, y) =
        (2 * √(2 * π * c11))⁻¹ * core m1 m2 c11 c12 c22 r x := by
    intro x
    have e : (fun y => density m1 m2 c11 c12 c22 (x, y)) = fun y =>
        (√(2 * π * c11))⁻¹ * exp (-(x - m1) ^ 2 / (2 * c11)) *
          ((√(2 * π * condVar c11 c12 c22))⁻¹ *
            exp (-(y - condMean m1 m2 c11 c12 x) ^ 2 / (2 * condVar c11 c12 c22))) :=
      funext (density_factor m1 m2 c11 c12 c22 hc hd x)
    have hneg : (-√(r ^ 2 - x ^ 2) - condMean m1 m2 c11 c12 x) /
          (√(condVar c11 c12 c22) * √2) =
        -((√(r ^ 2 - x ^ 2) + condMean m1 m2 c11 c12 x) / (√(condVar c11 c12 c22) * √2)) := by
      ring
    have hB : √(2 * π * condVar c11 c12 c22) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos pi_pos) hv)).ne'
    have hA : √(2 * π * c11) ≠ 0 :=
      (Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos pi_pos) hc)).ne'
    rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      gauss_window _ _ _ _ hv, hneg, RealErf.erf_neg]
    unfold core scaleK
    field_simp
    ring
  unfold pc
  rw [disk_integral _ (continuous_density m1 m2 c11 c12 c22) r hr,
    show (fun x => ∫ y in (-√(r ^ 2 - x ^ 2))..√(r ^ 2 - x ^ 2),
        density m1 m2 c11 c12 c22 (x, y)) =
      fun x => (2 * √(2 * π * c11))⁻¹ * core m1 m2 c11 c12 c22 r x from funext key,
    intervalIntegral.integral_const_mul]

/-- The integral over an interval of a function between `L` and `U` there is the width times a
number between `L` and `U`. -/
theorem integral_eq_width_mul {f : ℝ → ℝ} {a b L U : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h : ∀ x ∈ Icc a b, L ≤ f x ∧ f x ≤ U) :
    ∃ y, L ≤ y ∧ y ≤ U ∧ ∫ x in a..b, f x = (b - a) * y := by
  rcases hab.eq_or_lt with rfl | hlt
  · obtain ⟨h1, h2⟩ := h a ⟨le_rfl, le_rfl⟩
    exact ⟨L, le_rfl, h1.trans h2, by simp⟩
  · have hpos : 0 < b - a := sub_pos.mpr hlt
    have hL : (b - a) * L ≤ ∫ x in a..b, f x := by
      have hm := intervalIntegral.integral_mono_on hab
        (continuous_const.intervalIntegrable a b) hf fun x hx => (h x hx).1
      simpa using hm
    have hU : ∫ x in a..b, f x ≤ (b - a) * U := by
      have hm := intervalIntegral.integral_mono_on hab hf
        (continuous_const.intervalIntegrable a b) fun x hx => (h x hx).2
      simpa using hm
    refine ⟨(∫ x in a..b, f x) / (b - a), ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hpos]
      linarith
    · rw [div_le_iff₀ hpos]
      linarith
    · field_simp

#print axioms pc_eq
#print axioms integral_eq_width_mul

end Demos.Conjunction.Model
