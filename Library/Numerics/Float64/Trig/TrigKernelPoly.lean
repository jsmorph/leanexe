import LeanExe.ProofKit.TaylorRemainder

/-!
The approximation errors of fdlibm's sine and cosine kernel polynomials, as `Trig.kernelSin` and
`Trig.kernelCos` hold their coefficients, on `|x| ≤ 0.7854`, which contains `[-π/4, π/4]`.  With
`z = x ^ 2`, `x * eval sinKernel z` is `x + S1 x ^ 3 + ... + S6 x ^ 13` and `eval cosKernel z` is
`1 - x ^ 2/2 + C1 x ^ 4 + ... + C6 x ^ 14`.  Each bound compares the kernel polynomial with the
Taylor polynomial of degree 11 in `z` by `PolyBound.check`, which the kernel evaluates, and adds
the Taylor remainder.  fdlibm states `2 ^ -58` for the sine polynomial's error relative to `x`.
The largest error on `[0, 0.7854]` is about `2 ^ -57.994`, so `sin_kernel_error` states
`(65/64) 2 ^ -58`.  The cosine polynomial's largest error there is about `2 ^ -59.83`.
-/

namespace Library.Numerics.Float64.Trig.TrigKernelPoly
open LeanExe.ProofKit PolyBound TaylorRemainder

/-- `1 + S1 z + ... + S6 z ^ 6`, with the coefficients of `Trig.kernelSin`. -/
def sinKernel : List ℚ :=
  [1, ratOfWord 0xBFC5555555555549, ratOfWord 0x3F8111111110F8A6, ratOfWord 0xBF2A01A019C161D5,
    ratOfWord 0x3EC71DE357B1FE7D, ratOfWord 0xBE5AE5E68A2B9CEB, ratOfWord 0x3DE5D93A5ACFD57C]

/-- `1 - z/2 + C1 z ^ 2 + ... + C6 z ^ 7`, with the coefficients of `Trig.kernelCos`. -/
def cosKernel : List ℚ :=
  [1, -1 / 2, ratOfWord 0x3FA555555555554C, ratOfWord 0xBF56C16C16C15177,
    ratOfWord 0x3EFA01A019CB1590, ratOfWord 0xBE927E4F809C52AD, ratOfWord 0x3E21EE9EBDB4B1C4,
    ratOfWord 0xBDA8FAE9BE8838D4]

theorem sin_check :
    check (subP (sinCoeffs 12) sinKernel) 0 ((7854 / 10000) ^ 2) ((129 / 128) / 2 ^ 58) 14 =
      true := by
  decide +kernel

theorem cos_check :
    check (subP (cosCoeffs 12) cosKernel) 0 ((7854 / 10000) ^ 2) (1 / 2 ^ 59 - 1 / 2 ^ 70) 14 =
      true := by
  decide +kernel

theorem square_range (x : ℝ) (hx : |x| ≤ 7854 / 10000) :
    (((0 : ℚ)) : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ (((7854 / 10000 : ℚ) ^ 2 : ℚ) : ℝ) := by
  refine ⟨by simpa using sq_nonneg x, ?_⟩
  rw [← sq_abs]
  push_cast
  exact pow_le_pow_left₀ (abs_nonneg x) hx 2

/-- The sine kernel polynomial's error, relative to `x`. -/
theorem sin_kernel_error (x : ℝ) (hx : |x| ≤ 7854 / 10000) :
    |Real.sin x - x * eval sinKernel (x ^ 2)| ≤ |x| * ((65 / 64) / 2 ^ 58) := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have hr := sin_remainder x hx1 12
  obtain ⟨hz0, hz1⟩ := square_range x hx
  have hc := check_sound _ _ _ _ _ sin_check (x ^ 2) hz0 hz1
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
theorem cos_kernel_error (x : ℝ) (hx : |x| ≤ 7854 / 10000) :
    |Real.cos x - eval cosKernel (x ^ 2)| ≤ 1 / 2 ^ 59 := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have hr := cos_remainder x hx1 12
  obtain ⟨hz0, hz1⟩ := square_range x hx
  have hc := check_sound _ _ _ _ _ cos_check (x ^ 2) hz0 hz1
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

#print axioms sin_check
#print axioms cos_check
#print axioms sin_kernel_error
#print axioms cos_kernel_error

end Library.Numerics.Float64.Trig.TrigKernelPoly
