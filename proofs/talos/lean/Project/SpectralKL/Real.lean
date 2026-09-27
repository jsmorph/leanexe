import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace Project.SpectralKL
open MeasureTheory Set intervalIntegral

/-- Integral kernel in the KL moment functional, including its value at one. -/
noncomputable def kernel (t : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..1, (1-r) / (1+r*(t-1))

noncomputable def polynomial2 (d : ℝ) : ℝ := (1/12*d-1/6)*d+1/2

theorem kernel_one : kernel 1 = 1/2 := by
  simp only [kernel, sub_self, mul_zero, add_zero, div_one]
  rw [integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun r : ℝ => r)
    intervalIntegrable_const intervalIntegrable_id]
  norm_num [integral_id]

theorem weighted_power_integral (n : ℕ) :
    (∫ r in (0:ℝ)..1, r^n*(1-r)) = 1 / (((n:ℝ)+1)*((n:ℝ)+2)) := by
  have he : (fun r : ℝ => r^n*(1-r)) = (fun r => r^n-r^(n+1)) := by
    funext r; ring
  rw [he, intervalIntegral.integral_sub (f := fun r : ℝ => r^n)
    (g := fun r : ℝ => r^(n+1)) (intervalIntegrable_pow n) (intervalIntegrable_pow (n+1)),
    integral_pow, integral_pow]
  simp
  field_simp
  <;> ring

theorem polynomial2_integral (d : ℝ) :
    (∫ r in (0:ℝ)..1, (1-r)*(1-r*d+(r*d)^2)) = polynomial2 d := by
  have he : (fun r : ℝ => (1-r)*(1-r*d+(r*d)^2)) =
      (fun r => r^0*(1-r) - d*(r^1*(1-r)) + d^2*(r^2*(1-r))) := by
    funext r; ring
  have hi (n : ℕ) : IntervalIntegrable (fun r : ℝ => r^n*(1-r)) volume 0 1 :=
    (by fun_prop : Continuous (fun r : ℝ => r^n*(1-r))).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_add ((hi 0).sub ((hi 1).const_mul d))
    ((hi 2).const_mul (d^2)), intervalIntegral.integral_sub (hi 0) ((hi 1).const_mul d)]
  simp only [intervalIntegral.integral_const_mul, weighted_power_integral]
  norm_num [polynomial2]
  <;> ring

/-- The first nonconstant approximation has an error cubic in the displacement
from one. It is well-defined even when the direct log formula is 0/0. -/
theorem polynomial2_error (d : ℝ) (hd : |d| ≤ 1/2) :
    |kernel (1+d) - polynomial2 d| ≤ |d|^3/10 := by
  have hden (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : 1/2 ≤ 1+r*d := by
    have hb : |r*d| ≤ 1/2 := by
      rw [abs_mul, abs_of_nonneg hr.1]
      exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg d)).trans (by simpa using hd)
    linarith [(abs_le.mp hb).1]
  have hc : ContinuousOn (fun r : ℝ => (1-r)/(1+r*d)) (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro r hr
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hden r hr))
  have hi : IntervalIntegrable (fun r : ℝ => (1-r)/(1+r*d)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hp : IntervalIntegrable (fun r : ℝ => (1-r)*(1-r*d+(r*d)^2)) volume 0 1 :=
    (by fun_prop : Continuous (fun r : ℝ => (1-r)*(1-r*d+(r*d)^2))).intervalIntegrable _ _
  have hb (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      |(1-r)/(1+r*d) - (1-r)*(1-r*d+(r*d)^2)| ≤
        2*|d|^3*(r^3*(1-r)) := by
    have hpos : 0 < 1+r*d := lt_of_lt_of_le (by norm_num) (hden r hr)
    have he : (1-r)/(1+r*d) - (1-r)*(1-r*d+(r*d)^2) =
        -(1-r)*(r*d)^3/(1+r*d) := by field_simp; ring
    rw [he, abs_div, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hr.2),
      abs_pow, abs_mul, abs_of_nonneg hr.1, abs_of_pos hpos]
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg (pow_nonneg hr.1 3) (sub_nonneg.mpr hr.2),
      mul_nonneg (pow_nonneg (abs_nonneg d) 3)
        (mul_nonneg (pow_nonneg hr.1 3) (sub_nonneg.mpr hr.2)), hden r hr]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume) (a := (0:ℝ)) (b := 1) (by norm_num)
    (Filter.Eventually.of_forall (show ∀ r ∈ Ioc (0:ℝ) 1,
      ‖(1-r)/(1+r*d) - (1-r)*(1-r*d+(r*d)^2)‖ ≤ 2*|d|^3*(r^3*(1-r)) from
      fun r hr => by simpa [Real.norm_eq_abs] using hb r ⟨hr.1.le, hr.2⟩))
    ((by fun_prop : Continuous (fun r : ℝ => 2*|d|^3*(r^3*(1-r)))).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub hi hp, polynomial2_integral] at hbound
  simp only [intervalIntegral.integral_const_mul, weighted_power_integral,
    Real.norm_eq_abs] at hbound
  norm_num at hbound
  convert hbound using 1 <;> (try simp [kernel]) <;> ring

#print axioms polynomial2_error
end Project.SpectralKL
