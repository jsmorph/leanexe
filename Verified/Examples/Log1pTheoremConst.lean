import Verified.Examples.AtanTheoremConst
import LeanExe.ProofKit.LogRatioRemainder

/-!
Logarithms for `Log1p.log1p`'s proof.  `log (1 + v) = log (1 + s) - log (1 - s)` for
`s = v/(2 + v)`, so the series of `LogRatioRemainder.log_ratio_remainder` gives `log (1 + q)`
between rationals that the kernel computes for a rational `q`, and `ln2Hi + ln2Lo` within
`2 ^ -81` of `log 2` from the series at `s = 1/3`.
-/

namespace Verified.Examples.Log1pTheoremConst
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound AtanTheoremConst LogRatioRemainder

set_option exponentiation.threshold 4096

theorem log_ratio (v : ℝ) (hv : -1 < v) :
    Real.log (1 + v / (2 + v)) - Real.log (1 - v / (2 + v)) = Real.log (1 + v) := by
  have h2 : 0 < 2 + v := by linarith
  have h1 : 0 < 1 + v / (2 + v) := by
    rw [show 1 + v / (2 + v) = (2 + 2 * v) / (2 + v) by field_simp; ring]
    apply div_pos _ h2
    linarith
  have h1' : 0 < 1 - v / (2 + v) := by
    rw [show 1 - v / (2 + v) = 2 / (2 + v) by field_simp; ring]
    positivity
  rw [← Real.log_div h1.ne' h1'.ne']
  congr 1
  field_simp
  ring

/-- The lower end of the checked interval for `log (1 + q)`. -/
def logLo (q : ℚ) (n : ℕ) : ℚ :=
  q / (2 + q) * evalQ (logRatioCoeffs n) (q / (2 + q) * (q / (2 + q))) -
    2 * qabs (q / (2 + q)) ^ (2 * n + 1) / (1 - q / (2 + q) * (q / (2 + q)))

/-- The upper end of the checked interval for `log (1 + q)`. -/
def logHi (q : ℚ) (n : ℕ) : ℚ :=
  q / (2 + q) * evalQ (logRatioCoeffs n) (q / (2 + q) * (q / (2 + q))) +
    2 * qabs (q / (2 + q)) ^ (2 * n + 1) / (1 - q / (2 + q) * (q / (2 + q)))

theorem log_interval (q : ℚ) (hq : -1 / 2 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    ((logLo q n : ℚ) : ℝ) ≤ Real.log (1 + q) ∧ Real.log (1 + q) ≤ ((logHi q n : ℚ) : ℝ) := by
  have hq' : (-1 / 2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  have h2 : (0 : ℝ) < 2 + q := by linarith
  have hs : |(q : ℝ) / (2 + q)| < 1 := by
    rw [abs_div, abs_of_pos h2, div_lt_one h2, abs_lt]
    constructor <;> linarith
  have hr := log_ratio_remainder ((q : ℝ) / (2 + q)) hs n
  rw [log_ratio (q : ℝ) (by linarith)] at hr
  have he : ((q : ℝ) / (2 + q)) * eval (logRatioCoeffs n) (((q : ℝ) / (2 + q)) ^ 2) =
      ((q / (2 + q) * evalQ (logRatioCoeffs n) (q / (2 + q) * (q / (2 + q))) : ℚ) : ℝ) := by
    rw [show ((q : ℝ) / (2 + q)) ^ 2 = ((q / (2 + q) * (q / (2 + q)) : ℚ) : ℝ) by
      push_cast; ring, eval_cast]
    push_cast
    ring
  have hrem : 2 * |(q : ℝ) / (2 + q)| ^ (2 * n + 1) / (1 - ((q : ℝ) / (2 + q)) ^ 2) =
      ((2 * qabs (q / (2 + q)) ^ (2 * n + 1) / (1 - q / (2 + q) * (q / (2 + q))) : ℚ) : ℝ) := by
    have hc := qabs_cast (q / (2 + q))
    push_cast at hc ⊢
    rw [hc]
    ring
  rw [he, hrem] at hr
  obtain ⟨hab_l, hab_r⟩ := abs_le.mp hr
  constructor
  · simp only [logLo]
    push_cast at hab_l hab_r ⊢
    linarith
  · simp only [logHi]
    push_cast at hab_l hab_r ⊢
    linarith

theorem log_ge (q L : ℚ) (n : ℕ) (hq : -1 / 2 ≤ q) (hq1 : q ≤ 1) (h : L ≤ logLo q n) :
    (L : ℝ) ≤ Real.log (1 + q) :=
  (by exact_mod_cast h : (L : ℝ) ≤ (logLo q n : ℝ)).trans (log_interval q hq hq1 n).1

theorem log_le (q U : ℚ) (n : ℕ) (hq : -1 / 2 ≤ q) (hq1 : q ≤ 1) (h : logHi q n ≤ U) :
    Real.log (1 + q) ≤ (U : ℝ) :=
  (log_interval q hq hq1 n).2.trans (by exact_mod_cast h)

/-- `ln2Hi + ln2Lo` within `2 ^ -81` of `log 2`. -/
theorem ln2_close :
    |value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2| ≤ 1 / 2 ^ 81 := by
  have hl : Real.log (1 + (1 / 3 : ℚ)) - Real.log (1 - (1 / 3 : ℚ)) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hr := log_ratio_remainder ((1 / 3 : ℚ) : ℝ) (by norm_num) 30
  rw [hl] at hr
  have he : ((1 / 3 : ℚ) : ℝ) * eval (logRatioCoeffs 30) (((1 / 3 : ℚ) : ℝ) ^ 2) =
      (((1 / 3) * evalQ (logRatioCoeffs 30) (1 / 9) : ℚ) : ℝ) := by
    rw [show ((1 / 3 : ℚ) : ℝ) ^ 2 = ((1 / 9 : ℚ) : ℝ) by norm_num, eval_cast]
    push_cast
    ring
  rw [he] at hr
  have hc := words_close 0x3FE62E42FEE00000 0x3DEA39EF35793C76
    ((1 / 3) * evalQ (logRatioCoeffs 30) (1 / 9)) (1 / 2 ^ 82) (by decide +kernel)
  have hn : 2 * |((1 / 3 : ℚ) : ℝ)| ^ (2 * 30 + 1) / (1 - ((1 / 3 : ℚ) : ℝ) ^ 2) ≤ 1 / 2 ^ 82 := by
    norm_num
  have hr' := hr.trans hn
  set q : ℝ := (((1 / 3) * evalQ (logRatioCoeffs 30) (1 / 9) : ℚ) : ℝ)
  have h2 := abs_sub_le (value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76) q (Real.log 2)
  rw [abs_sub_comm q (Real.log 2)] at h2
  calc |value 0x3FE62E42FEE00000 + value 0x3DEA39EF35793C76 - Real.log 2|
      ≤ ((1 / 2 ^ 82 : ℚ) : ℝ) + 1 / 2 ^ 82 := h2.trans (add_le_add hc hr')
    _ = 1 / 2 ^ 81 := by norm_num

#print axioms log_interval
#print axioms ln2_close

end Verified.Examples.Log1pTheoremConst
