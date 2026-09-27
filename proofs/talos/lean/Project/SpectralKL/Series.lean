import Project.SpectralKL.Real
import Mathlib.Algebra.Ring.GeomSum

namespace Project.SpectralKL
open MeasureTheory Set intervalIntegral

noncomputable def series (n : ℕ) (d : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-d)^k / (((k:ℝ)+1)*((k:ℝ)+2))

theorem series_integral (n : ℕ) (d : ℝ) :
    (∫ r in (0:ℝ)..1, (1-r)*(∑ k ∈ Finset.range n, (-r*d)^k)) = series n d := by
  have he : (fun r : ℝ => (1-r)*(∑ k ∈ Finset.range n, (-r*d)^k)) =
      (fun r => ∑ k ∈ Finset.range n, (-d)^k*(r^k*(1-r))) := by
    funext r
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show -r*d = r*(-d) by ring, mul_pow]
    ring
  rw [he, intervalIntegral.integral_finsetSum]
  · unfold series
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, weighted_power_integral]
    ring
  · intro k _
    exact (by fun_prop : Continuous (fun r : ℝ => (-d)^k*(r^k*(1-r)))).intervalIntegrable 0 1

/-- A reusable geometric-series remainder for any truncation length. -/
theorem series_error (n : ℕ) (d : ℝ) (hd : |d| ≤ 1/2) :
    |kernel (1+d) - series n d| ≤ 2*|d|^n / (((n:ℝ)+1)*((n:ℝ)+2)) := by
  have hden (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : 1/2 ≤ 1+r*d := by
    have hb : |r*d| ≤ 1/2 := by
      rw [abs_mul, abs_of_nonneg hr.1]
      exact (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg d)).trans (by simpa using hd)
    linarith [(abs_le.mp hb).1]
  have hi : IntervalIntegrable (fun r : ℝ => (1-r)/(1+r*d)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro r hr
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hden r hr))
  have hp : IntervalIntegrable
      (fun r : ℝ => (1-r)*(∑ k ∈ Finset.range n, (-r*d)^k)) volume 0 1 :=
    (by fun_prop : Continuous
      (fun r : ℝ => (1-r)*(∑ k ∈ Finset.range n, (-r*d)^k))).intervalIntegrable _ _
  have hb (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      |(1-r)/(1+r*d) - (1-r)*(∑ k ∈ Finset.range n, (-r*d)^k)| ≤
        2*|d|^n*(r^n*(1-r)) := by
    have hpos : 0 < 1+r*d := lt_of_lt_of_le (by norm_num) (hden r hr)
    have hg := geom_sum_mul_neg (-r*d) n
    have he : (1-r)/(1+r*d) - (1-r)*(∑ k ∈ Finset.range n, (-r*d)^k) =
        (1-r)*(-r*d)^n/(1+r*d) := by
      apply (eq_div_iff hpos.ne').mpr
      rw [sub_mul, div_mul_cancel₀ _ hpos.ne']
      have hg' : (∑ k ∈ Finset.range n, (-r*d)^k)*(1+r*d) = 1-(-r*d)^n := by
        convert hg using 1 <;> ring
      linear_combination -(1-r)*hg'
    rw [he, abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hr.2),
      abs_pow, abs_mul, abs_neg, abs_of_nonneg hr.1, abs_of_pos hpos]
    calc
      _ ≤ (1-r)*(r*|d|)^n/(1/2) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (sub_nonneg.mpr hr.2) (pow_nonneg (mul_nonneg hr.1 (abs_nonneg d)) n))
          (by norm_num) (hden r hr)
      _ = _ := by rw [mul_pow]; ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume) (a := (0:ℝ)) (b := 1) (by norm_num)
    (Filter.Eventually.of_forall (show ∀ r ∈ Ioc (0:ℝ) 1,
      ‖(1-r)/(1+r*d) - (1-r)*(∑ k ∈ Finset.range n, (-r*d)^k)‖ ≤
        2*|d|^n*(r^n*(1-r)) from
      fun r hr => by simpa [Real.norm_eq_abs] using hb r ⟨hr.1.le, hr.2⟩))
    ((by fun_prop : Continuous (fun r : ℝ => 2*|d|^n*(r^n*(1-r)))).intervalIntegrable 0 1)
  rw [integral_sub hi hp, series_integral] at hbound
  simp only [intervalIntegral.integral_const_mul, weighted_power_integral, Real.norm_eq_abs] at hbound
  simpa [kernel, div_eq_mul_inv] using hbound

theorem series41_error (d : ℝ) (hd : |d| ≤ 1/2) :
    |series 41 d - kernel (1+d)| ≤ 1/1000000000000000 := by
  have h := series_error 41 d hd
  have hp := pow_le_pow_left₀ (abs_nonneg d) hd 41
  rw [abs_sub_comm]
  apply h.trans
  norm_num at hp ⊢
  linarith

#print axioms series_error
#print axioms series41_error
end Project.SpectralKL
