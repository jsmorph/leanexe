import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Verified.Examples.FFTComplex

theorem norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem norm_le_of_coordinate_relative (z w : ℂ) (e : ℝ) (he : 0 ≤ e)
    (hr : |z.re| ≤ e * |w.re|) (hi : |z.im| ≤ e * |w.im|) :
    ‖z‖ ≤ e * ‖w‖ := by
  have hr2 : z.re ^ 2 ≤ e ^ 2 * w.re ^ 2 := by
    have h := mul_le_mul hr hr (abs_nonneg z.re) (mul_nonneg he (abs_nonneg w.re))
    simpa only [← sq, sq_abs, mul_pow] using h
  have hi2 : z.im ^ 2 ≤ e ^ 2 * w.im ^ 2 := by
    have h := mul_le_mul hi hi (abs_nonneg z.im) (mul_nonneg he (abs_nonneg w.im))
    simpa only [← sq, sq_abs, mul_pow] using h
  have hsq : ‖z‖ ^ 2 ≤ (e * ‖w‖) ^ 2 := by
    rw [norm_sq z, mul_pow, norm_sq w]
    nlinarith only [hr2, hi2]
  nlinarith only [hsq, norm_nonneg z, mul_nonneg he (norm_nonneg w)]

theorem component_sum_le (z : ℂ) : |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (|z.re| + |z.im|) ^ 2 ≤ (Real.sqrt 2 * ‖z‖) ^ 2 := by
    rw [mul_pow, hsqrt, norm_sq z]
    nlinarith [sq_abs z.re, sq_abs z.im, sq_nonneg (|z.re| - |z.im|)]
  nlinarith [abs_nonneg z.re, abs_nonneg z.im,
    mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg z)]

theorem sqrt_two_twice_le_three : 2 * Real.sqrt 2 ≤ 3 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

theorem product_error_norm (z error : ℂ) (q h : ℝ) (hq : 1 ≤ q) (hh : 0 ≤ h)
    (hr : |error.re| ≤ (q - 1) * (|z.re| + |z.im|) + 2 * h)
    (hi : |error.im| ≤ (q - 1) * (|z.re| + |z.im|) + 2 * h) :
    ‖error‖ ≤ 2 * (q - 1) * ‖z‖ + 3 * h := by
  have hq0 : 0 ≤ q - 1 := sub_nonneg.mpr hq
  calc
    ‖error‖ ≤ Real.sqrt 2 * max |error.re| |error.im| :=
      Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * ((q - 1) * (|z.re| + |z.im|) + 2 * h) :=
      mul_le_mul_of_nonneg_left (max_le hr hi) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * ((q - 1) * (Real.sqrt 2 * ‖z‖) + 2 * h) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (component_sum_le z) hq0) le_rfl)
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt 2) ^ 2 * (q - 1) * ‖z‖ + (2 * Real.sqrt 2) * h := by ring
    _ ≤ 2 * (q - 1) * ‖z‖ + 3 * h := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right sqrt_two_twice_le_three hh)

#print axioms norm_le_of_coordinate_relative
#print axioms component_sum_le
#print axioms product_error_norm

end Verified.Examples.FFTComplex
