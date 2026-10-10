import LeanExe.ProofKit.LogRatioRemainder
import LeanExe.ProofKit.PolyChecks

/-!
The approximation error of fdlibm's `log1p` polynomial, as FreeBSD msun's `s_log1p.c` at commit
`20381bce4b63975494a2f4bc84257f6932e6d379` holds its coefficients `Lp1` to `Lp7`.  With
`s = f/(2 + f)` and `z = s ^ 2`, `log (1 + f) = log (1 + s) - log (1 - s) = 2 s + s R(z)`, and the
code approximates `R(z)` by `Lp1 z + ... + Lp7 z ^ 7`, so that `s * eval log1pKernel z` is
`2 s + s (Lp1 z + ... + Lp7 z ^ 7)`.  The thresholds of `s_log1p.c` keep `1 + f` within about
`[√2/2, √2]`, where `|s| ≤ 0.171574`, inside the bound `0.1716` that the source states.  The source
bounds the polynomial's error by `2 ^ -58.45`.  The largest error on `[0, 0.1716]` is about
`2 ^ -58.47`, at `s ≈ 0.168`, and `log1p_kernel_error` states `(93/128) 2 ^ -58`, about
`2 ^ -58.46`, relative to `s`.
-/

namespace Verified.Examples.Log1pKernelPoly
open LeanExe.ProofKit PolyBound PolyChecks LogRatioRemainder

/-- `2 + Lp1 z + ... + Lp7 z ^ 7`. -/
def log1pKernel : List ℚ :=
  [2, ratOfWord 0x3FE5555555555593, ratOfWord 0x3FD999999997FA04, ratOfWord 0x3FD2492494229359,
    ratOfWord 0x3FCC71C51D8E78AF, ratOfWord 0x3FC7466496CB03DE, ratOfWord 0x3FC39A09D078C69F,
    ratOfWord 0x3FC2F112DF3E5244]

/-- The Taylor polynomial of degree 19 in `z` minus the kernel polynomial. -/
def log1pDiff : List ℚ := subP (logRatioCoeffs 20) log1pKernel

/-- The checked bound on `log1pDiff`. -/
def log1pEps : ℚ := (185 / 256) / 2 ^ 58

theorem log1p_part_1 : check log1pDiff (0 : ℚ) (15439 / 4194304 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_2 : check log1pDiff (15439 / 4194304 : ℚ) (15439 / 2097152 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_3 : check log1pDiff (15439 / 2097152 : ℚ) (46317 / 4194304 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_4 : check log1pDiff (46317 / 4194304 : ℚ) (15439 / 1048576 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_5 : check log1pDiff (15439 / 1048576 : ℚ) (77195 / 4194304 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_6 : check log1pDiff (77195 / 4194304 : ℚ) (46317 / 2097152 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_7 : check log1pDiff (46317 / 2097152 : ℚ) (108073 / 4194304 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_8 : check log1pDiff (108073 / 4194304 : ℚ) (15439 / 524288 : ℚ) log1pEps 18 = true := by
  decide +kernel

theorem log1p_part_covers : Covers log1pDiff log1pEps 18 (0 : ℚ) (15439 / 524288 : ℚ)
    [(15439 / 4194304 : ℚ), (15439 / 2097152 : ℚ), (46317 / 4194304 : ℚ), (15439 / 1048576 : ℚ), (77195 / 4194304 : ℚ), (46317 / 2097152 : ℚ), (108073 / 4194304 : ℚ)] :=
  ⟨log1p_part_1, log1p_part_2, log1p_part_3, log1p_part_4, log1p_part_5, log1p_part_6, log1p_part_7, log1p_part_8⟩

/-- The `log1p` polynomial's error, relative to `s`. -/
theorem log1p_kernel_error (s : ℝ) (hs : |s| ≤ 1716 / 10000) :
    |Real.log (1 + s) - Real.log (1 - s) - s * eval log1pKernel (s ^ 2)| ≤
      |s| * ((93 / 128) / 2 ^ 58) := by
  have hs1 : |s| < 1 := hs.trans_lt (by norm_num)
  have hr := log_ratio_remainder s hs1 20
  have hz0 : (((0 : ℚ)) : ℝ) ≤ s ^ 2 := by simpa using sq_nonneg s
  have hs2 : s ^ 2 ≤ (1716 / 10000) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg s) hs 2
  have hz1 : s ^ 2 ≤ (((15439 / 524288 : ℚ)) : ℝ) := by
    push_cast
    have : (1716 / 10000 : ℝ) ^ 2 ≤ 15439 / 524288 := by norm_num
    linarith
  have hc := bounded_of_covers _ _ _ _ _ _ log1p_part_covers (s ^ 2) hz0 hz1
  rw [log1pDiff, eval_subP] at hc
  have hc' : |eval (logRatioCoeffs 20) (s ^ 2) - eval log1pKernel (s ^ 2)| ≤
      (185 / 256) / 2 ^ 58 :=
    hc.trans (le_of_eq (by norm_num [log1pEps]))
  have hd : |s * eval (logRatioCoeffs 20) (s ^ 2) - s * eval log1pKernel (s ^ 2)| ≤
      |s| * ((185 / 256) / 2 ^ 58) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hc' (abs_nonneg s)
  have ht : 2 * |s| ^ (2 * 20 + 1) / (1 - s ^ 2) ≤ |s| * ((1 / 256) / 2 ^ 58) := by
    have h1 : (9 / 10 : ℝ) ≤ 1 - s ^ 2 := by nlinarith
    have hp : |s| ^ 40 ≤ (1716 / 10000) ^ 40 := pow_le_pow_left₀ (abs_nonneg s) hs 40
    rw [div_le_iff₀ (by linarith), pow_succ]
    calc 2 * (|s| ^ 40 * |s|) = (2 * |s| ^ 40) * |s| := by ring
      _ ≤ ((1 / 256) / 2 ^ 58 * (1 - s ^ 2)) * |s| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg s)
          calc 2 * |s| ^ 40 ≤ (1 / 256) / 2 ^ 58 * (9 / 10) := by
                have : 2 * (1716 / 10000 : ℝ) ^ 40 ≤ (1 / 256) / 2 ^ 58 * (9 / 10) := by norm_num
                linarith
            _ ≤ (1 / 256) / 2 ^ 58 * (1 - s ^ 2) := by gcongr
      _ = |s| * ((1 / 256) / 2 ^ 58) * (1 - s ^ 2) := by ring
  calc |Real.log (1 + s) - Real.log (1 - s) - s * eval log1pKernel (s ^ 2)| ≤
      |Real.log (1 + s) - Real.log (1 - s) - s * eval (logRatioCoeffs 20) (s ^ 2)| +
        |s * eval (logRatioCoeffs 20) (s ^ 2) - s * eval log1pKernel (s ^ 2)| := abs_sub_le _ _ _
    _ ≤ |s| * ((1 / 256) / 2 ^ 58) + |s| * ((185 / 256) / 2 ^ 58) := add_le_add (hr.trans ht) hd
    _ = |s| * ((93 / 128) / 2 ^ 58) := by ring

#print axioms log1p_part_covers
#print axioms log1p_kernel_error

end Verified.Examples.Log1pKernelPoly
