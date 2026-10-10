import LeanExe.ProofKit.TaylorRemainder

/-!
The approximation errors of the two polynomials of Arm's `log`, as `Log.logCore` and
`Log.logNear1` hold their coefficients, relative to `r`.  `r * eval coreKernel r` is
`r + A0 r ^ 2 + ... + A4 r ^ 6`, used for `|r| ≤ 1/256`, and `r * eval near1Kernel r` is
`r + B0 r ^ 2 + ... + B10 r ^ 12`, used for `r = x - 1` with `x` from `1 - 2 ^ -4` to below
`1 + 0x1.09p-4`.  Each bound compares the polynomial with the Taylor polynomial of
`log (1 + r) / r` by `PolyBound.check` and adds the Taylor remainder.  The largest relative
errors are about `2 ^ -54.96` at `r = ±1/256` and `2 ^ -62.15` at `r = -1/16`.
-/

namespace Verified.Examples.LogKernelPoly
open LeanExe.ProofKit PolyBound TaylorRemainder

/-- `1 + A0 r + ... + A4 r ^ 5`, with the coefficients of `Log.logCore`. -/
def coreKernel : List ℚ :=
  [1, ratOfWord 0xBFE0000000000001, ratOfWord 0x3FD555555551305B, ratOfWord 0xBFCFFFFFFFEB4590,
    ratOfWord 0x3FC999B324F10111, ratOfWord 0xBFC55575E506C89F]

/-- `1 + B0 r + ... + B10 r ^ 11`, with the coefficients of `Log.logNear1`. -/
def near1Kernel : List ℚ :=
  [1, ratOfWord 0xBFE0000000000000, ratOfWord 0x3FD5555555555577, ratOfWord 0xBFCFFFFFFFFFFDCB,
    ratOfWord 0x3FC999999995DD0C, ratOfWord 0xBFC55555556745A7, ratOfWord 0x3FC24924A344DE30,
    ratOfWord 0xBFBFFFFFA4423D65, ratOfWord 0x3FBC7184282AD6CA, ratOfWord 0xBFB999EB43B068FF,
    ratOfWord 0x3FB78182F7AFD085, ratOfWord 0xBFB5521375D145CD]

theorem core_check :
    check (subP (log1pQuotCoeffs 12) coreKernel) (-1 / 256) (1 / 256) ((135 / 256) / 2 ^ 54) 16 =
      true := by
  decide +kernel

theorem near1_check :
    check (subP (log1pQuotCoeffs 20) near1Kernel) (-1 / 16) (265 / 4096) ((59 / 64) / 2 ^ 62)
      16 = true := by
  decide +kernel

/-- The error of `Log.logCore`'s polynomial, relative to `r`. -/
theorem core_kernel_error (r : ℝ) (hr : |r| ≤ 1 / 256) :
    |Real.log (1 + r) - r * eval coreKernel r| ≤ |r| * ((17 / 32) / 2 ^ 54) := by
  have hr1 : |r| < 1 := hr.trans_lt (by norm_num)
  have hrem := log1p_remainder r hr1 12
  rw [eval_log1pCoeffs] at hrem
  obtain ⟨hlo, hhi⟩ := abs_le.mp hr
  have hc := check_sound _ _ _ _ _ core_check r (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP] at hc
  have hc' : |eval (log1pQuotCoeffs 12) r - eval coreKernel r| ≤ (135 / 256) / 2 ^ 54 :=
    hc.trans (le_of_eq (by norm_num))
  have hd : |r * eval (log1pQuotCoeffs 12) r - r * eval coreKernel r| ≤
      |r| * ((135 / 256) / 2 ^ 54) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hc' (abs_nonneg r)
  have ht : |r| ^ (12 + 1) / (1 - |r|) ≤ |r| * ((1 / 256) / 2 ^ 54) := by
    have h1 : 0 < 1 - |r| := by linarith
    have h2 : (255 / 256 : ℝ) ≤ 1 - |r| := by linarith
    have hp : |r| ^ 12 ≤ (1 / 256) ^ 12 := pow_le_pow_left₀ (abs_nonneg r) hr 12
    rw [div_le_iff₀ h1, pow_succ]
    calc |r| ^ 12 * |r| ≤ ((1 / 256) / 2 ^ 54 * (1 - |r|)) * |r| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg r)
          calc |r| ^ 12 ≤ (1 / 256) / 2 ^ 54 * (255 / 256) := hp.trans (by norm_num)
            _ ≤ (1 / 256) / 2 ^ 54 * (1 - |r|) := by gcongr
      _ = |r| * ((1 / 256) / 2 ^ 54) * (1 - |r|) := by ring
  calc |Real.log (1 + r) - r * eval coreKernel r| ≤
      |Real.log (1 + r) - r * eval (log1pQuotCoeffs 12) r| +
        |r * eval (log1pQuotCoeffs 12) r - r * eval coreKernel r| := abs_sub_le _ _ _
    _ ≤ |r| * ((1 / 256) / 2 ^ 54) + |r| * ((135 / 256) / 2 ^ 54) := add_le_add (hrem.trans ht) hd
    _ = |r| * ((17 / 32) / 2 ^ 54) := by ring

/-- The error of `Log.logNear1`'s polynomial, relative to `r`. -/
theorem near1_kernel_error (r : ℝ) (hlo : -1 / 16 ≤ r) (hhi : r ≤ 265 / 4096) :
    |Real.log (1 + r) - r * eval near1Kernel r| ≤ |r| * ((15 / 16) / 2 ^ 62) := by
  have hr : |r| ≤ 265 / 4096 := abs_le.mpr ⟨by linarith, hhi⟩
  have hr1 : |r| < 1 := hr.trans_lt (by norm_num)
  have hrem := log1p_remainder r hr1 20
  rw [eval_log1pCoeffs] at hrem
  have hc := check_sound _ _ _ _ _ near1_check r (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP] at hc
  have hc' : |eval (log1pQuotCoeffs 20) r - eval near1Kernel r| ≤ (59 / 64) / 2 ^ 62 :=
    hc.trans (le_of_eq (by norm_num))
  have hd : |r * eval (log1pQuotCoeffs 20) r - r * eval near1Kernel r| ≤
      |r| * ((59 / 64) / 2 ^ 62) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hc' (abs_nonneg r)
  have ht : |r| ^ (20 + 1) / (1 - |r|) ≤ |r| * ((1 / 64) / 2 ^ 62) := by
    have h1 : 0 < 1 - |r| := by linarith
    have h2 : (3831 / 4096 : ℝ) ≤ 1 - |r| := by linarith
    have hp : |r| ^ 20 ≤ (265 / 4096) ^ 20 := pow_le_pow_left₀ (abs_nonneg r) hr 20
    rw [div_le_iff₀ h1, pow_succ]
    calc |r| ^ 20 * |r| ≤ ((1 / 64) / 2 ^ 62 * (1 - |r|)) * |r| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg r)
          calc |r| ^ 20 ≤ (1 / 64) / 2 ^ 62 * (3831 / 4096) := hp.trans (by norm_num)
            _ ≤ (1 / 64) / 2 ^ 62 * (1 - |r|) := by gcongr
      _ = |r| * ((1 / 64) / 2 ^ 62) * (1 - |r|) := by ring
  calc |Real.log (1 + r) - r * eval near1Kernel r| ≤
      |Real.log (1 + r) - r * eval (log1pQuotCoeffs 20) r| +
        |r * eval (log1pQuotCoeffs 20) r - r * eval near1Kernel r| := abs_sub_le _ _ _
    _ ≤ |r| * ((1 / 64) / 2 ^ 62) + |r| * ((59 / 64) / 2 ^ 62) := add_le_add (hrem.trans ht) hd
    _ = |r| * ((15 / 16) / 2 ^ 62) := by ring

#print axioms core_check
#print axioms near1_check
#print axioms core_kernel_error
#print axioms near1_kernel_error

end Verified.Examples.LogKernelPoly
