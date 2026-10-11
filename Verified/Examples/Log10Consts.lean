import Verified.Examples.Log2KernelPoly
import Verified.Examples.LogTables
import Verified.Examples.Log1pKernelPoly
import LeanExe.ProofKit.LogRatioRemainder

/-!
The constants of fdlibm's `log10` against `log 10`.  `log 10 = 3 log 2 + log (5/4)`, and
`log (5/4) = log (1 + 1/9) - log (1 - 1/9)` is the sum of 20 terms of the series of `atanh` within
`2 ^ -120`, so with the split of `log 2` from `ExpReductionBounds` the rational `lnTenQ` lies within
`2 ^ -89` of `log 10`.  The kernel checks that `ivln10hi + ivln10lo` and `log10_2hi + log10_2lo`
agree with `1 / lnTenQ` and `S / lnTenQ` closely enough that they lie within `2 ^ -86` of
`1 / log 10` and `log 2 / log 10`.  `log_one_add_lower` bounds `|log (1 + f)|` below by `2 |s|` for
`s = f / (2 + f)`, from `Log1pKernelPoly.log1p_kernel_error`.
-/

namespace Verified.Examples.Log10Consts
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound LogRatioRemainder LogTables

/-- `log (5/4)` by 20 terms of the series of `log (1 + s) - log (1 - s)` at `s = 1/9`. -/
def logFiveFourthsQ : ℚ := 1 / 9 * evalQ (logRatioCoeffs 20) (1 / 81)

/-- `3 log 2 + log (5/4)`, within `2 ^ -89` of `log 10`. -/
def lnTenQ : ℚ := 3 * ExpReductionBounds.splitLogTwo + logFiveFourthsQ

theorem log_five_fourths : |Real.log (5 / 4) - (logFiveFourthsQ : ℝ)| ≤ 1 / 2 ^ 120 := by
  have h := log_ratio_remainder (1 / 9) (by rw [abs_of_pos (by norm_num)]; norm_num) 20
  have h1 : Real.log (1 + 1 / 9) - Real.log (1 - 1 / 9) = Real.log (5 / 4) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h2 : (1 / 9 : ℝ) * eval (logRatioCoeffs 20) ((1 / 9) ^ 2) = (logFiveFourthsQ : ℝ) := by
    rw [logFiveFourthsQ, Rat.cast_mul, evalQ_cast]
    norm_num
  rw [h1, h2] at h
  refine h.trans ?_
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 9)]
  norm_num

theorem log_ten : |Real.log 10 - (lnTenQ : ℝ)| ≤ 1 / 2 ^ 89 := by
  obtain ⟨hS, -⟩ := Log2KernelPoly.split_bounds
  have h5 := log_five_fourths
  have h10 : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have hq : (lnTenQ : ℝ) = 3 * (ExpReductionBounds.splitLogTwo : ℝ) + (logFiveFourthsQ : ℝ) := by
    rw [lnTenQ]
    push_cast
    ring
  rw [h10, hq]
  rw [abs_le] at hS h5 ⊢
  constructor <;> nlinarith [hS.1, hS.2, h5.1, h5.2]

theorem const_checks :
    qabs ((ratOfWord 0x3FDBCB7B15200000 + ratOfWord 0x3DBB9438CA9AADD5) * lnTenQ - 1) ≤
      1 / 2 ^ 87 ∧
    qabs ((ratOfWord 0x3FD34413509F6000 + ratOfWord 0x3D59FEF311F12B36) * lnTenQ -
      ExpReductionBounds.splitLogTwo) ≤ 1 / 2 ^ 88 ∧
    (2302 / 1000 : ℚ) ≤ lnTenQ - 1 / 2 ^ 89 ∧ lnTenQ + 1 / 2 ^ 89 ≤ 2303 / 1000 ∧
    ratOfWord 0x3FDBCB7B15200000 + ratOfWord 0x3DBB9438CA9AADD5 ≤ 4343 / 10000 ∧
    ratOfWord 0x3FD34413509F6000 + ratOfWord 0x3D59FEF311F12B36 ≤ 302 / 1000 := by
  decide +kernel

theorem log_ten_bounds : (2302 / 1000 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2303 / 1000 := by
  obtain ⟨-, -, h1, h2, -, -⟩ := const_checks
  have h := abs_le.mp log_ten
  have h1' : ((2302 / 1000 : ℚ) : ℝ) ≤ ((lnTenQ - 1 / 2 ^ 89 : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((lnTenQ + 1 / 2 ^ 89 : ℚ) : ℝ) ≤ ((2303 / 1000 : ℚ) : ℝ) := Rat.cast_le.mpr h2
  push_cast at h1' h2'
  constructor <;> linarith [h.1, h.2]

/-- `ivln10hi + ivln10lo` lies within `2 ^ -86` of `1 / log 10`. -/
theorem inv_ln_ten :
    |value 0x3FDBCB7B15200000 + value 0x3DBB9438CA9AADD5 - 1 / Real.log 10| ≤ 1 / 2 ^ 86 := by
  obtain ⟨c1, -, -, -, c5, -⟩ := const_checks
  obtain ⟨hl1, -⟩ := log_ten_bounds
  have hlt := log_ten
  set I := value (0x3FDBCB7B15200000 : UInt64) + value 0x3DBB9438CA9AADD5 with hI
  have hIq : ((ratOfWord 0x3FDBCB7B15200000 + ratOfWord 0x3DBB9438CA9AADD5 : ℚ) : ℝ) = I := by
    rw [Rat.cast_add, ratOfWord_cast, ratOfWord_cast]
  have hc1 : |I * (lnTenQ : ℝ) - 1| ≤ 1 / 2 ^ 87 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr c1
    rw [qabs_cast] at h
    push_cast at h
    rw [ratOfWord_cast, ratOfWord_cast] at h
    exact h.trans (by norm_num)
  have hI0 : 0 ≤ I := by
    have h := Rat.cast_le (K := ℝ) |>.mpr (show (0 : ℚ) ≤ ratOfWord 0x3FDBCB7B15200000 +
      ratOfWord 0x3DBB9438CA9AADD5 by decide +kernel)
    rw [hIq] at h
    push_cast at h
    exact h
  have hc5 : I ≤ 4343 / 10000 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr c5
    rw [hIq] at h
    exact h.trans (by norm_num)
  have hpos : 0 < Real.log 10 := by linarith
  have hdiff : |I * Real.log 10 - 1| ≤ 1 / 2 ^ 87 + 4343 / 10000 * (1 / 2 ^ 89) := by
    have h3 : |I * (Real.log 10 - (lnTenQ : ℝ))| ≤ 4343 / 10000 * (1 / 2 ^ 89) := by
      rw [abs_mul, abs_of_nonneg hI0]
      exact mul_le_mul hc5 hlt (abs_nonneg _) (by norm_num)
    calc |I * Real.log 10 - 1| = |(I * (lnTenQ : ℝ) - 1) + I * (Real.log 10 - (lnTenQ : ℝ))| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hc1 h3)
  rw [show I - 1 / Real.log 10 = (I * Real.log 10 - 1) / Real.log 10 by field_simp,
    abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have : (1 : ℝ) / 2 ^ 87 + 4343 / 10000 * (1 / 2 ^ 89) ≤ 1 / 2 ^ 86 * (2302 / 1000) := by
    norm_num
  nlinarith

/-- `log10_2hi + log10_2lo` lies within `2 ^ -86` of `log 2 / log 10`. -/
theorem log_two_ten :
    |value 0x3FD34413509F6000 + value 0x3D59FEF311F12B36 - Real.log 2 / Real.log 10| ≤
      1 / 2 ^ 86 := by
  obtain ⟨-, c2, -, -, -, c6⟩ := const_checks
  obtain ⟨hl1, -⟩ := log_ten_bounds
  obtain ⟨hS, -⟩ := Log2KernelPoly.split_bounds
  have hlt := log_ten
  set L := value (0x3FD34413509F6000 : UInt64) + value 0x3D59FEF311F12B36 with hL
  have hLq : ((ratOfWord 0x3FD34413509F6000 + ratOfWord 0x3D59FEF311F12B36 : ℚ) : ℝ) = L := by
    rw [Rat.cast_add, ratOfWord_cast, ratOfWord_cast]
  have hc2 : |L * (lnTenQ : ℝ) - (ExpReductionBounds.splitLogTwo : ℝ)| ≤ 1 / 2 ^ 88 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr c2
    rw [qabs_cast] at h
    push_cast at h
    rw [ratOfWord_cast, ratOfWord_cast] at h
    exact h.trans (by norm_num)
  have hL0 : 0 ≤ L := by
    have h := Rat.cast_le (K := ℝ) |>.mpr (show (0 : ℚ) ≤ ratOfWord 0x3FD34413509F6000 +
      ratOfWord 0x3D59FEF311F12B36 by decide +kernel)
    rw [hLq] at h
    push_cast at h
    exact h
  have hc6 : L ≤ 302 / 1000 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr c6
    rw [hLq] at h
    exact h.trans (by norm_num)
  have hpos : 0 < Real.log 10 := by linarith
  have hdiff : |L * Real.log 10 - Real.log 2| ≤
      1 / 2 ^ 88 + 302 / 1000 * (1 / 2 ^ 89) + 1 / 2 ^ 92 := by
    have h3 : |L * (Real.log 10 - (lnTenQ : ℝ))| ≤ 302 / 1000 * (1 / 2 ^ 89) := by
      rw [abs_mul, abs_of_nonneg hL0]
      exact mul_le_mul hc6 hlt (abs_nonneg _) (by norm_num)
    have h4 : |(ExpReductionBounds.splitLogTwo : ℝ) - Real.log 2| ≤ 1 / 2 ^ 92 := by
      rw [abs_sub_comm]
      exact hS
    calc |L * Real.log 10 - Real.log 2| = |(L * (lnTenQ : ℝ) - (ExpReductionBounds.splitLogTwo : ℝ)) +
          L * (Real.log 10 - (lnTenQ : ℝ)) + ((ExpReductionBounds.splitLogTwo : ℝ) - Real.log 2)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hc2 h3)) h4)
  rw [show L - Real.log 2 / Real.log 10 = (L * Real.log 10 - Real.log 2) / Real.log 10 by
    field_simp, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have : (1 : ℝ) / 2 ^ 88 + 302 / 1000 * (1 / 2 ^ 89) + 1 / 2 ^ 92 ≤ 1 / 2 ^ 86 * (2302 / 1000) := by
    norm_num
  nlinarith

theorem eval_nonneg (p : List ℚ) (hp : ∀ c ∈ p, 0 ≤ c) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ eval p x := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [eval_cons]
    have ha : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hp a (List.mem_cons_self ..)
    have hrest := ih (fun c hc => hp c (List.mem_cons_of_mem a hc))
    have := mul_nonneg hx hrest
    linarith

/-- `|log (1 + f)| ≥ 2 (1 - 2 ^ -58) |s|` for `s = f / (2 + f)` with `|s| ≤ 0.1716`: the kernel
polynomial `2 + Lg1 s ^ 2 + ...` is at least 2, and its error is below `2 ^ -57 |s|`. -/
theorem log_one_add_lower (f : ℝ) (hf : -1 < f) (hs : |f / (2 + f)| ≤ 1716 / 10000) :
    2 * (1 - 1 / 2 ^ 58) * |f / (2 + f)| ≤ |Real.log (1 + f)| := by
  set s := f / (2 + f) with hsdef
  have h2f : 0 < 2 + f := by linarith
  have hk := Log1pKernelPoly.log1p_kernel_error s hs
  have hsplit : Real.log (1 + s) - Real.log (1 - s) = Real.log (1 + f) := by
    have h1 : 0 < 1 + s := by
      have := (abs_le.mp hs).1
      linarith
    have h2 : 0 < 1 - s := by
      have := (abs_le.mp hs).2
      linarith
    rw [← Real.log_div h1.ne' h2.ne']
    congr 1
    rw [hsdef]
    field_simp
    ring
  rw [hsplit] at hk
  have hcoef : ∀ c ∈ (Log1pKernelPoly.log1pKernel.drop 1), 0 ≤ c := by decide +kernel
  have hpoly : 2 ≤ eval Log1pKernelPoly.log1pKernel (s ^ 2) := by
    have h := eval_nonneg _ hcoef (s ^ 2) (sq_nonneg s)
    have he : eval Log1pKernelPoly.log1pKernel (s ^ 2) =
        2 + s ^ 2 * eval (Log1pKernelPoly.log1pKernel.drop 1) (s ^ 2) := by
      simp only [Log1pKernelPoly.log1pKernel, List.drop_succ_cons, List.drop_zero, eval_cons]
      push_cast
      ring
    rw [he]
    have := mul_nonneg (sq_nonneg s) h
    linarith
  have hsk : 2 * |s| ≤ |s * eval Log1pKernelPoly.log1pKernel (s ^ 2)| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < eval Log1pKernelPoly.log1pKernel (s ^ 2))]
    nlinarith [abs_nonneg s]
  have h3 := abs_sub_abs_le_abs_sub (s * eval Log1pKernelPoly.log1pKernel (s ^ 2))
    (Real.log (1 + f))
  rw [abs_sub_comm] at h3
  have h4 : |s| * ((93 / 128) / 2 ^ 58) ≤ 2 * (1 / 2 ^ 58) * |s| := by
    nlinarith [abs_nonneg s]
  nlinarith [abs_nonneg s]

#print axioms log_five_fourths
#print axioms log_ten
#print axioms const_checks
#print axioms inv_ln_ten
#print axioms log_two_ten
#print axioms eval_nonneg
#print axioms log_one_add_lower

end Verified.Examples.Log10Consts
