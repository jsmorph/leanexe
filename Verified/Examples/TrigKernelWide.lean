import Verified.Examples.TrigKernelPoly

/-!
The approximation errors of the kernel polynomials of `TrigKernelPoly` on `|x| ≤ 0.78541`.
`Trig.remPio2` returns reduced arguments up to `π/4 + 4.8 · 10 ^ -6`, beyond the range
`|x| ≤ 0.7854` of `TrigKernelPoly`.  The largest errors lie inside `[0, 0.7854]`, so the
allowances there hold unchanged on the wider range.
-/

namespace Verified.Examples.TrigKernelWide
open LeanExe.ProofKit PolyBound TaylorRemainder TrigKernelPoly

theorem sin_check_wide :
    check (subP (sinCoeffs 12) sinKernel) 0 ((78541 / 100000) ^ 2) ((129 / 128) / 2 ^ 58) 14 =
      true := by
  decide +kernel

theorem cos_check_wide :
    check (subP (cosCoeffs 12) cosKernel) 0 ((78541 / 100000) ^ 2) (1 / 2 ^ 59 - 1 / 2 ^ 70) 14 =
      true := by
  decide +kernel

theorem square_range_wide (x : ℝ) (hx : |x| ≤ 78541 / 100000) :
    (((0 : ℚ)) : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ (((78541 / 100000 : ℚ) ^ 2 : ℚ) : ℝ) := by
  refine ⟨by simpa using sq_nonneg x, ?_⟩
  rw [← sq_abs]
  push_cast
  exact pow_le_pow_left₀ (abs_nonneg x) hx 2

/-- The sine kernel polynomial's error, relative to `x`. -/
theorem sin_kernel_error_wide (x : ℝ) (hx : |x| ≤ 78541 / 100000) :
    |Real.sin x - x * eval sinKernel (x ^ 2)| ≤ |x| * ((65 / 64) / 2 ^ 58) := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have hr := sin_remainder x hx1 12
  obtain ⟨hz0, hz1⟩ := square_range_wide x hx
  have hc := check_sound _ _ _ _ _ sin_check_wide (x ^ 2) hz0 hz1
  rw [eval_subP] at hc
  have hd : |x * eval (sinCoeffs 12) (x ^ 2) - x * eval sinKernel (x ^ 2)| ≤
      |x| * ((129 / 128) / 2 ^ 58) := by
    rw [← mul_sub, abs_mul]
    have hc' : |eval (sinCoeffs 12) (x ^ 2) - eval sinKernel (x ^ 2)| ≤ (129 / 128) / 2 ^ 58 :=
      hc.trans (le_of_eq (by norm_num))
    exact mul_le_mul_of_nonneg_left hc' (abs_nonneg x)
  have hp : |x| ^ (2 * 12 + 1) ≤ |x| := by
    rw [pow_succ']
    exact mul_le_of_le_one_right (abs_nonneg x) (pow_le_one₀ (abs_nonneg x) hx1)
  have ht : 2 * |x| ^ (2 * 12 + 1) / ((2 * 12 + 1).factorial : ℝ) ≤ |x| * (1 / 2 ^ 65) := by
    have hf : (2 : ℝ) / ((2 * 12 + 1).factorial : ℝ) ≤ 1 / 2 ^ 65 := by
      norm_num [Nat.factorial]
    calc 2 * |x| ^ (2 * 12 + 1) / ((2 * 12 + 1).factorial : ℝ) =
        |x| ^ (2 * 12 + 1) * (2 / ((2 * 12 + 1).factorial : ℝ)) := by ring
      _ ≤ |x| * (1 / 2 ^ 65) := by
        apply mul_le_mul hp hf (by positivity) (abs_nonneg x)
  calc |Real.sin x - x * eval sinKernel (x ^ 2)| ≤
      |Real.sin x - x * eval (sinCoeffs 12) (x ^ 2)| +
        |x * eval (sinCoeffs 12) (x ^ 2) - x * eval sinKernel (x ^ 2)| := abs_sub_le _ _ _
    _ ≤ |x| * (1 / 2 ^ 65) + |x| * ((129 / 128) / 2 ^ 58) := add_le_add (hr.trans ht) hd
    _ = |x| * ((65 / 64) / 2 ^ 58) := by ring

/-- The cosine kernel polynomial's absolute error. -/
theorem cos_kernel_error_wide (x : ℝ) (hx : |x| ≤ 78541 / 100000) :
    |Real.cos x - eval cosKernel (x ^ 2)| ≤ 1 / 2 ^ 59 := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have hr := cos_remainder x hx1 12
  obtain ⟨hz0, hz1⟩ := square_range_wide x hx
  have hc := check_sound _ _ _ _ _ cos_check_wide (x ^ 2) hz0 hz1
  rw [eval_subP] at hc
  have hc' : |eval (cosCoeffs 12) (x ^ 2) - eval cosKernel (x ^ 2)| ≤ 1 / 2 ^ 59 - 1 / 2 ^ 70 :=
    hc.trans (le_of_eq (by norm_num))
  have hp : |x| ^ (2 * 12) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
  have ht : 2 * |x| ^ (2 * 12) / ((2 * 12).factorial : ℝ) ≤ 1 / 2 ^ 70 := by
    have hf : (2 : ℝ) / ((2 * 12).factorial : ℝ) ≤ 1 / 2 ^ 70 := by
      norm_num [Nat.factorial]
    calc 2 * |x| ^ (2 * 12) / ((2 * 12).factorial : ℝ) =
        |x| ^ (2 * 12) * (2 / ((2 * 12).factorial : ℝ)) := by ring
      _ ≤ 1 * (1 / 2 ^ 70) := by
        apply mul_le_mul hp hf (by positivity) zero_le_one
      _ = 1 / 2 ^ 70 := one_mul _
  calc |Real.cos x - eval cosKernel (x ^ 2)| ≤
      |Real.cos x - eval (cosCoeffs 12) (x ^ 2)| +
        |eval (cosCoeffs 12) (x ^ 2) - eval cosKernel (x ^ 2)| := abs_sub_le _ _ _
    _ ≤ 1 / 2 ^ 70 + (1 / 2 ^ 59 - 1 / 2 ^ 70) := add_le_add (hr.trans ht) hc'
    _ = 1 / 2 ^ 59 := by ring

#print axioms sin_check_wide
#print axioms cos_check_wide
#print axioms sin_kernel_error_wide
#print axioms cos_kernel_error_wide

end Verified.Examples.TrigKernelWide
