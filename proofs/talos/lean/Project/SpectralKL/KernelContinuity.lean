import Project.SpectralKL.Real

namespace Project.SpectralKL
open MeasureTheory Set intervalIntegral

theorem kernel_denominator (t r : ℝ) (ht : |t-1| ≤ 1/2) (hr : r ∈ Icc (0:ℝ) 1) :
    1/2 ≤ 1+r*(t-1) := by
  have h : |r*(t-1)| ≤ 1/2 := by
    rw [abs_mul, abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans (by simpa using ht)
  linarith [(abs_le.mp h).1]

theorem kernel_integrable (t : ℝ) (ht : |t-1| ≤ 1/2) :
    IntervalIntegrable (fun r : ℝ => (1-r)/(1+r*(t-1))) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro r hr
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) (kernel_denominator t r ht hr))

theorem kernel_abs_le (t : ℝ) (ht : |t-1| ≤ 1/2) : |kernel t| ≤ 1 := by
  have hp (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      |(1-r)/(1+r*(t-1))| ≤ 2*(1-r) := by
    have hd := kernel_denominator t r ht hr
    rw [abs_div, abs_of_nonneg (sub_nonneg.mpr hr.2), abs_of_pos (by linarith : 0 < 1+r*(t-1))]
    apply (div_le_iff₀ (by linarith : 0 < 1+r*(t-1))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hr.2)]
  have h := intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume) (a := (0:ℝ)) (b := 1) (by norm_num)
    (Filter.Eventually.of_forall (show ∀ r ∈ Ioc (0:ℝ) 1,
      ‖(1-r)/(1+r*(t-1))‖ ≤ 2*(1-r) from
      fun r hr => by simpa only [Real.norm_eq_abs] using hp r ⟨hr.1.le,hr.2⟩))
    ((by fun_prop : Continuous (fun r : ℝ => 2*(1-r))).intervalIntegrable 0 1)
  have hi : (∫ r in (0:ℝ)..1, (1-r)) = 1/2 := by
    simpa using weighted_power_integral 0
  simpa only [kernel, Real.norm_eq_abs, intervalIntegral.integral_const_mul, hi, mul_one_div, div_self (by norm_num : (2:ℝ) ≠ 0)] using h

theorem kernel_lipschitz (t u : ℝ) (ht : |t-1| ≤ 1/2) (hu : |u-1| ≤ 1/2) :
    |kernel t-kernel u| ≤ 4*|t-u| := by
  have hp (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      |(1-r)/(1+r*(t-1))-(1-r)/(1+r*(u-1))| ≤ 4*|t-u| := by
    have ha := kernel_denominator t r ht hr
    have hb := kernel_denominator u r hu hr
    have ha0 : 0 < 1+r*(t-1) := by linarith
    have hb0 : 0 < 1+r*(u-1) := by linarith
    have hprod : 1/4 ≤ (1+r*(t-1))*(1+r*(u-1)) := by nlinarith
    have hid : (1-r)/(1+r*(t-1))-(1-r)/(1+r*(u-1)) =
        (1-r)*r*(u-t)/((1+r*(t-1))*(1+r*(u-1))) := by
      field_simp; ring
    rw [hid, abs_div, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr.2),
      abs_of_nonneg hr.1, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm u t]
    apply (div_le_iff₀ (mul_pos ha0 hb0)).mpr
    have hfactor : (1-r)*r ≤ 1 := by nlinarith [hr.2, sq_nonneg r]
    nlinarith [mul_le_mul_of_nonneg_right hfactor (abs_nonneg (t-u)),
      mul_le_mul_of_nonneg_right hprod (abs_nonneg (t-u))]
  have h := intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume) (a := (0:ℝ)) (b := 1) (by norm_num)
    (Filter.Eventually.of_forall (show ∀ r ∈ Ioc (0:ℝ) 1,
      ‖(1-r)/(1+r*(t-1))-(1-r)/(1+r*(u-1))‖ ≤ 4*|t-u| from
      fun r hr => by simpa only [Real.norm_eq_abs] using hp r ⟨hr.1.le,hr.2⟩))
    (intervalIntegrable_const (a := (0:ℝ)) (b := 1))
  rw [integral_sub (kernel_integrable t ht) (kernel_integrable u hu)] at h
  simpa [kernel, Real.norm_eq_abs] using h

#print axioms kernel_lipschitz
end Project.SpectralKL
