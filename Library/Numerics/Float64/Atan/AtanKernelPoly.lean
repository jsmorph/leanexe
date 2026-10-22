import LeanExe.ProofKit.TaylorRemainder
import LeanExe.ProofKit.PolyChecks

/-!
The approximation error of fdlibm's arctangent polynomial, as FreeBSD msun's `s_atan.c` at commit
`20381bce4b63975494a2f4bc84257f6932e6d379` holds its coefficients `aT[0]` to `aT[10]`.  The code
returns `x - x * (s1 + s2)` with `s1 + s2 = aT[0] z + ... + aT[10] z ^ 11` and `z = x ^ 2`, so
`x * eval atanKernel (x ^ 2)` is that value in exact arithmetic.  The reduced argument satisfies
`|x| < 0.4375`: the code takes the polynomial directly below `0x3fdc0000`, and its reductions
give `|x| ≤ 16/39` or less on the other intervals.  `s_atan.c` states no error bound.  The largest
error relative to `x` on `[0, 7/16]` is about `2 ^ -57.71`, at `x ≈ 0.188`.
-/

namespace Library.Numerics.Float64.Atan.AtanKernelPoly
open LeanExe.ProofKit PolyBound PolyChecks TaylorRemainder

/-- `1 - aT[0] z - ... - aT[10] z ^ 11`. -/
def atanKernel : List ℚ :=
  [1, -ratOfWord 0x3FD555555555550D, -ratOfWord 0xBFC999999998EBC4,
    -ratOfWord 0x3FC24924920083FF, -ratOfWord 0xBFBC71C6FE231671, -ratOfWord 0x3FB745CDC54C206E,
    -ratOfWord 0xBFB3B0F2AF749A6D, -ratOfWord 0x3FB10D66A0D03D51, -ratOfWord 0xBFADDE2D52DEFD9A,
    -ratOfWord 0x3FA97B4B24760DEB, -ratOfWord 0xBFA2B4442C6A6C2F, -ratOfWord 0x3F90AD3AE322DA11]

/-- The Taylor polynomial of degree 29 in `z` minus the kernel polynomial. -/
def atanDiff : List ℚ := subP (atanCoeffs 30) atanKernel

/-- The checked bound on `atanDiff`. -/
def atanEps : ℚ := (159 / 256) / 2 ^ 57

theorem atan_part_1 : check atanDiff (0 : ℚ) (49 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_2 : check atanDiff (49 / 4096 : ℚ) (49 / 2048 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_3 : check atanDiff (49 / 2048 : ℚ) (147 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_4 : check atanDiff (147 / 4096 : ℚ) (49 / 1024 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_5 : check atanDiff (49 / 1024 : ℚ) (245 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_6 : check atanDiff (245 / 4096 : ℚ) (147 / 2048 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_7 : check atanDiff (147 / 2048 : ℚ) (343 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_8 : check atanDiff (343 / 4096 : ℚ) (49 / 512 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_9 : check atanDiff (49 / 512 : ℚ) (441 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_10 : check atanDiff (441 / 4096 : ℚ) (245 / 2048 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_11 : check atanDiff (245 / 2048 : ℚ) (539 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_12 : check atanDiff (539 / 4096 : ℚ) (147 / 1024 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_13 : check atanDiff (147 / 1024 : ℚ) (637 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_14 : check atanDiff (637 / 4096 : ℚ) (343 / 2048 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_15 : check atanDiff (343 / 2048 : ℚ) (735 / 4096 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_16 : check atanDiff (735 / 4096 : ℚ) (49 / 256 : ℚ) atanEps 18 = true := by
  decide +kernel

theorem atan_part_covers : Covers atanDiff atanEps 18 (0 : ℚ) (49 / 256 : ℚ)
    [(49 / 4096 : ℚ), (49 / 2048 : ℚ), (147 / 4096 : ℚ), (49 / 1024 : ℚ), (245 / 4096 : ℚ), (147 / 2048 : ℚ), (343 / 4096 : ℚ), (49 / 512 : ℚ), (441 / 4096 : ℚ), (245 / 2048 : ℚ), (539 / 4096 : ℚ), (147 / 1024 : ℚ), (637 / 4096 : ℚ), (343 / 2048 : ℚ), (735 / 4096 : ℚ)] :=
  ⟨atan_part_1, atan_part_2, atan_part_3, atan_part_4, atan_part_5, atan_part_6, atan_part_7, atan_part_8, atan_part_9, atan_part_10, atan_part_11, atan_part_12, atan_part_13, atan_part_14, atan_part_15, atan_part_16⟩

/-- The arctangent polynomial's error, relative to `x`. -/
theorem atan_kernel_error (x : ℝ) (hx : |x| ≤ 7 / 16) :
    |Real.arctan x - x * eval atanKernel (x ^ 2)| ≤ |x| * ((5 / 8) / 2 ^ 57) := by
  have hx1 : |x| < 1 := hx.trans_lt (by norm_num)
  have hr := atan_remainder x hx1 30
  have hx2 : x ^ 2 ≤ (7 / 16) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hz0 : (((0 : ℚ)) : ℝ) ≤ x ^ 2 := by simpa using sq_nonneg x
  have hz1 : x ^ 2 ≤ (((49 / 256 : ℚ)) : ℝ) := by
    push_cast
    linarith
  have hc := bounded_of_covers _ _ _ _ _ _ atan_part_covers (x ^ 2) hz0 hz1
  rw [atanDiff, eval_subP] at hc
  have hc' : |eval (atanCoeffs 30) (x ^ 2) - eval atanKernel (x ^ 2)| ≤ (159 / 256) / 2 ^ 57 :=
    hc.trans (le_of_eq (by norm_num [atanEps]))
  have hd : |x * eval (atanCoeffs 30) (x ^ 2) - x * eval atanKernel (x ^ 2)| ≤
      |x| * ((159 / 256) / 2 ^ 57) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hc' (abs_nonneg x)
  have ht : |x| ^ (2 * 30 + 1) / (1 - x ^ 2) ≤ |x| * ((1 / 256) / 2 ^ 57) := by
    have h1 : (207 / 256 : ℝ) ≤ 1 - x ^ 2 := by nlinarith
    have hp : |x| ^ 60 ≤ (7 / 16) ^ 60 := pow_le_pow_left₀ (abs_nonneg x) hx 60
    rw [div_le_iff₀ (by linarith), pow_succ]
    calc |x| ^ 60 * |x| ≤ ((1 / 256) / 2 ^ 57 * (1 - x ^ 2)) * |x| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
          calc |x| ^ 60 ≤ (1 / 256) / 2 ^ 57 * (207 / 256) := hp.trans (by norm_num)
            _ ≤ (1 / 256) / 2 ^ 57 * (1 - x ^ 2) := by gcongr
      _ = |x| * ((1 / 256) / 2 ^ 57) * (1 - x ^ 2) := by ring
  calc |Real.arctan x - x * eval atanKernel (x ^ 2)| ≤
      |Real.arctan x - x * eval (atanCoeffs 30) (x ^ 2)| +
        |x * eval (atanCoeffs 30) (x ^ 2) - x * eval atanKernel (x ^ 2)| := abs_sub_le _ _ _
    _ ≤ |x| * ((1 / 256) / 2 ^ 57) + |x| * ((159 / 256) / 2 ^ 57) := add_le_add (hr.trans ht) hd
    _ = |x| * ((5 / 8) / 2 ^ 57) := by ring

#print axioms atan_part_covers
#print axioms atan_kernel_error

end Library.Numerics.Float64.Atan.AtanKernelPoly
