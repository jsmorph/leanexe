import LeanExe.ProofKit.GammaStirling
import LeanExe.ProofKit.RatExpLog
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The overflow thresholds of CORE-MATH's `tgamma` and `lgamma`, from Stirling's series with twelve
terms (`GammaStirling.stirling_twelve`) and rational enclosures of `log 2`, `log (π/2)`, and the
logarithms of the thresholds' significands (`RatExpLog`), with `π` from Mathlib's 20-digit bounds.

`tgamma` returns `+∞` for `x ≥ t0 = 0x1.573fae561f648p+7` (`tgamma.c` line 709), and
`gamma_overflow` gives `Γ x ≥ 2 ^ 1024` there, beyond the largest double plus half its spacing.
`lgamma` treats `|x| ≥ x1 = 0x1.754d9278b51a6p+1014` apart (`lgamma.c` lines 874-895): it returns
the double below the largest at `x1`, the largest at the next double `x2`, and `+∞` from `x3`, the
double after `x2`.  With `u = 2 ^ 971` the spacing of the largest doubles, `lgamma_x1` puts
`lgamma x1` within `3 u/5` of `2 ^ 1024 - 2 u`, `lgamma_x2` puts `lgamma x2` within `u/5` of
`2 ^ 1024 - u`, and `lgamma_overflow` gives `lgamma x ≥ 2 ^ 1024 - u/2` for `x ≥ x3`.  Each
threshold is also identified with its binary64 word by `ratOfWord`.
-/

namespace LeanExe.ProofKit.GammaThresholds

open Real PolyBound RatExpLog GammaBasic GammaStirling

set_option exponentiation.threshold 4096

/-- A lower bound on `log 2`, within `2 ^ -99`. -/
def log2Lo : ℚ := 878668439483319573618263538047 / 2 ^ 100

/-- An upper bound on `log 2`, within `2 ^ -99`. -/
def log2Hi : ℚ := 439334219741659786809131769025 / 2 ^ 99

/-- A lower bound on `log (π/2)`. -/
def logHalfPiLo : ℚ := 286224543706432541748243995613 / 2 ^ 99

/-- An upper bound on `log (π/2)`. -/
def logHalfPiHi : ℚ := 572449087412865083500523048411 / 2 ^ 100

theorem log_two_lo : (log2Lo : ℝ) ≤ log 2 := by
  have h := le_log 2 log2Lo 40 (by norm_num) (by decide +kernel) (by decide +kernel)
  rwa [Rat.cast_ofNat] at h

theorem log_two_hi : log 2 ≤ (log2Hi : ℝ) := by
  have h := log_le 2 log2Hi 40 (by norm_num) (by decide +kernel) (by norm_num) (by decide +kernel)
  rwa [Rat.cast_ofNat] at h

theorem log_half_pi_lo : (logHalfPiLo : ℝ) ≤ log (π / 2) := by
  have h := le_log (314159265358979323846 / 10 ^ 20 / 2) logHalfPiLo 40 (by norm_num)
    (by decide +kernel) (by decide +kernel)
  have hp : ((314159265358979323846 / 10 ^ 20 / 2 : ℚ) : ℝ) ≤ π / 2 := by
    have := pi_gt_d20
    push_cast
    norm_num at this ⊢
    linarith
  exact h.trans (log_le_log (by positivity) hp)

theorem log_half_pi_hi : log (π / 2) ≤ (logHalfPiHi : ℝ) := by
  have h := log_le (314159265358979323847 / 10 ^ 20 / 2) logHalfPiHi 40 (by norm_num)
    (by decide +kernel) (by norm_num) (by decide +kernel)
  have hp : π / 2 ≤ ((314159265358979323847 / 10 ^ 20 / 2 : ℚ) : ℝ) := by
    have := pi_lt_d20
    push_cast
    norm_num at this ⊢
    linarith
  exact (log_le_log (by positivity) hp).trans h

theorem log_two_pi : log (2 * π) = 2 * log 2 + log (π / 2) := by
  rw [show 2 * π = 2 ^ 2 * (π / 2) by ring, log_mul (by positivity) (by positivity), log_pow]
  push_cast
  ring

theorem log_two_pow_mul (k : ℕ) {a : ℝ} (ha : 0 < a) : log (2 ^ k * a) = k * log 2 + log a := by
  rw [log_mul (by positivity) ha.ne', log_pow]

theorem lgamma_mono {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : lgamma a ≤ lgamma b :=
  log_le_log (Gamma_pos_of_pos (by linarith))
    (Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (by linarith)) hab)

theorem abs_series_le {x : ℝ} (hx : 16 ≤ x) : |series stirCoeffs x| ≤ 1 := by
  have hc : check stirCoeffs 0 (1 / 256) 2 0 = true := by decide +kernel
  have hx0 : 0 < x := by linarith
  have hi0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hinv : x⁻¹ ≤ 1 / 16 := by
    rw [inv_le_comm₀ hx0 (by norm_num)]
    norm_num
    linarith
  have hz1 : x⁻¹ ^ 2 ≤ ((1 / 256 : ℚ) : ℝ) := by
    have := pow_le_pow_left₀ hi0.le hinv 2
    push_cast
    norm_num at this ⊢
    linarith
  have he := check_sound stirCoeffs 0 (1 / 256) 2 0 hc (x⁻¹ ^ 2) (by push_cast; positivity) hz1
  rw [series, abs_mul, abs_of_pos hi0]
  push_cast at he
  calc x⁻¹ * |eval stirCoeffs (x⁻¹ ^ 2)| ≤ 1 / 16 * 2 :=
        mul_le_mul hinv he (abs_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

/-- Bounds on `lgamma x` for `x ≥ 16` from bounds on `log x`, with the terms below 5 absorbed. -/
theorem lgamma_between {x llo lhi : ℝ} (hx : 16 ≤ x) (hlo : llo ≤ log x) (hhi : log x ≤ lhi) :
    (x - 1 / 2) * llo - x - 2 ≤ lgamma x ∧ lgamma x ≤ (x - 1 / 2) * lhi - x + 5 := by
  have hst := stirling_twelve hx
  have hs := abs_series_le hx
  have hx1 : 0 < x - 1 := by linarith
  have hE : 104001 / (25 * (x - 1) ^ 25) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (15 : ℝ) ^ 25 ≤ (x - 1) ^ 25 := pow_le_pow_left₀ (by norm_num) (by linarith) 25
    norm_num at this ⊢
    linarith
  have h2pi0 : 0 ≤ log (2 * π) := log_nonneg (by nlinarith [pi_gt_three])
  have h2pi1 : log (2 * π) ≤ 2 * π - 1 := log_le_sub_one_of_pos (by positivity)
  have hpi := pi_lt_d2
  have hm1 : (x - 1 / 2) * llo ≤ (x - 1 / 2) * log x := mul_le_mul_of_nonneg_left hlo (by linarith)
  have hm2 : (x - 1 / 2) * log x ≤ (x - 1 / 2) * lhi := mul_le_mul_of_nonneg_left hhi (by linarith)
  rw [abs_le] at hst hs
  simp only [lead] at hst
  constructor <;> linarith

/-- `0x1.573fae561f648p+7`, the threshold from which `tgamma` overflows. -/
def t0 : ℚ := 0x1573fae561f648 / 2 ^ 45

theorem t0_word : ratOfWord 0x406573FAE561F648 = t0 := by decide +kernel

/-- A lower bound on `log (t0/128)`. -/
def logT0Lo : ℚ := 371773994577497577092832276405 / 2 ^ 100

theorem lgamma_t0 : 1024 * log 2 ≤ lgamma t0 := by
  have ht16 : (16 : ℝ) ≤ t0 := by norm_num [t0]
  have hst := stirling_twelve ht16
  have hlt : (logT0Lo : ℝ) ≤ log ((t0 / 128 : ℚ) : ℝ) :=
    le_log (t0 / 128) logT0Lo 40 (by norm_num) (by decide +kernel) (by decide +kernel)
  have hlog : log (t0 : ℝ) = 7 * log 2 + log ((t0 / 128 : ℚ) : ℝ) := by
    rw [show (t0 : ℝ) = 2 ^ 7 * ((t0 / 128 : ℚ) : ℝ) by push_cast; ring,
      log_two_pow_mul 7 (by norm_num [t0])]
    norm_num
  have hS : series stirCoeffs t0 = (t0 : ℝ)⁻¹ * ((qeval stirCoeffs (t0⁻¹ ^ 2) : ℚ) : ℝ) := by
    rw [series, qeval_cast]
    push_cast
    rfl
  have hcheck : 1024 * log2Hi ≤ (t0 - 1 / 2) * (7 * log2Lo + logT0Lo) - t0 +
      (2 * log2Lo + logHalfPiLo) / 2 + t0⁻¹ * qeval stirCoeffs (t0⁻¹ ^ 2) -
      104001 / (25 * (t0 - 1) ^ 25) := by decide +kernel
  have hcr : ((1024 * log2Hi : ℚ) : ℝ) ≤ (((t0 - 1 / 2) * (7 * log2Lo + logT0Lo) - t0 +
      (2 * log2Lo + logHalfPiLo) / 2 + t0⁻¹ * qeval stirCoeffs (t0⁻¹ ^ 2) -
      104001 / (25 * (t0 - 1) ^ 25) : ℚ) : ℝ) := by exact_mod_cast hcheck
  push_cast at hcr
  rw [← hS] at hcr
  have hl2 := log_two_lo
  have hl2' := log_two_hi
  have hlp := log_half_pi_lo
  have h12 : (0 : ℝ) < (t0 : ℝ) - 1 / 2 := by norm_num [t0]
  have hm : ((t0 : ℝ) - 1 / 2) * (7 * log2Lo + logT0Lo) ≤ ((t0 : ℝ) - 1 / 2) * log (t0 : ℝ) := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_left (by linarith) h12.le
  rw [abs_le] at hst
  simp only [lead, log_two_pi] at hst
  linarith

theorem gamma_t0 : (2 : ℝ) ^ 1024 ≤ Gamma t0 := by
  have hpos : 0 < Gamma t0 := Gamma_pos_of_pos (by norm_num [t0])
  have h := exp_le_exp.mpr lgamma_t0
  rw [lgamma, exp_log hpos] at h
  have he := RealExpError.exp_pow_two 1024
  push_cast at he
  rwa [he] at h

/-- `Γ x ≥ 2 ^ 1024` from `tgamma`'s overflow threshold on. -/
theorem gamma_overflow {x : ℝ} (hx : (t0 : ℝ) ≤ x) : (2 : ℝ) ^ 1024 ≤ Gamma x := by
  have ht : (2 : ℝ) ≤ t0 := by norm_num [t0]
  exact gamma_t0.trans (Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr ht)
    (Set.mem_Ici.mpr (by linarith)) hx)

/-- `0x1.754d9278b51a6p+1014`, from which `lgamma` treats its argument apart. -/
def x1 : ℚ := 0x1754d9278b51a6 * 2 ^ 962

/-- The double after `x1`. -/
def x2 : ℚ := 0x1754d9278b51a7 * 2 ^ 962

/-- The double after `x2`, from which `lgamma` overflows. -/
def x3 : ℚ := 0x1754d9278b51a8 * 2 ^ 962

theorem x1_word : ratOfWord 0x7F5754D9278B51A6 = x1 := by decide +kernel

theorem x2_word : ratOfWord 0x7F5754D9278B51A7 = x2 := by decide +kernel

theorem x3_word : ratOfWord 0x7F5754D9278B51A8 = x3 := by decide +kernel

theorem log_huge {m : ℚ} (hm : 0 < m) (lo hi : ℚ) (hlo : (lo : ℝ) ≤ log ((m / 2 ^ 52 : ℚ) : ℝ))
    (hhi : log ((m / 2 ^ 52 : ℚ) : ℝ) ≤ hi) :
    1014 * (log2Lo : ℝ) + lo ≤ log ((m * 2 ^ 962 : ℚ) : ℝ) ∧
      log ((m * 2 ^ 962 : ℚ) : ℝ) ≤ 1014 * (log2Hi : ℝ) + hi := by
  have hpos : (0 : ℝ) < ((m / 2 ^ 52 : ℚ) : ℝ) := by exact_mod_cast div_pos hm (by positivity)
  have he : log ((m * 2 ^ 962 : ℚ) : ℝ) = 1014 * log 2 + log ((m / 2 ^ 52 : ℚ) : ℝ) := by
    rw [show ((m * 2 ^ 962 : ℚ) : ℝ) = 2 ^ 1014 * ((m / 2 ^ 52 : ℚ) : ℝ) by push_cast; ring,
      log_two_pow_mul 1014 hpos]
    norm_num
  rw [he]
  have := log_two_lo
  have := log_two_hi
  constructor <;> linarith

theorem lgamma_x1 : |lgamma x1 - (2 ^ 1024 - 2 ^ 972)| ≤ 3 / 5 * 2 ^ 971 := by
  have hl := log_huge (m := 0x1754d9278b51a6) (by norm_num)
    (478174312879680717139350438317 / 2 ^ 100) (29885894554980044821209402395 / 2 ^ 96)
    (le_log _ _ 40 (by norm_num) (by decide +kernel) (by decide +kernel))
    (log_le _ _ 40 (by norm_num) (by decide +kernel) (by norm_num) (by decide +kernel))
  have hx : (16 : ℝ) ≤ ((0x1754d9278b51a6 * 2 ^ 962 : ℚ) : ℝ) := by norm_num
  obtain ⟨h1, h2⟩ := lgamma_between hx hl.1 hl.2
  have hc : (2 ^ 1024 - 2 ^ 972 - 3 / 5 * 2 ^ 971 : ℚ) ≤
      (0x1754d9278b51a6 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Lo + 478174312879680717139350438317 / 2 ^ 100) -
        0x1754d9278b51a6 * 2 ^ 962 - 2 ∧
      (0x1754d9278b51a6 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Hi + 29885894554980044821209402395 / 2 ^ 96) -
        0x1754d9278b51a6 * 2 ^ 962 + 5 ≤ (2 ^ 1024 - 2 ^ 972 + 3 / 5 * 2 ^ 971 : ℚ) := by
    decide +kernel
  have hc1 := hc.1
  have hc2 := hc.2
  have r1 : ((2 ^ 1024 - 2 ^ 972 - 3 / 5 * 2 ^ 971 : ℚ) : ℝ) ≤ ((
      (0x1754d9278b51a6 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Lo + 478174312879680717139350438317 / 2 ^ 100) -
        0x1754d9278b51a6 * 2 ^ 962 - 2 : ℚ) : ℝ) := by exact_mod_cast hc1
  have r2 : (((0x1754d9278b51a6 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Hi + 29885894554980044821209402395 / 2 ^ 96) -
        0x1754d9278b51a6 * 2 ^ 962 + 5 : ℚ) : ℝ) ≤
      ((2 ^ 1024 - 2 ^ 972 + 3 / 5 * 2 ^ 971 : ℚ) : ℝ) := by exact_mod_cast hc2
  push_cast at r1 r2 h1 h2
  rw [x1, abs_le]
  push_cast
  constructor <;> linarith

theorem lgamma_x2 : |lgamma x2 - (2 ^ 1024 - 2 ^ 971)| ≤ 1 / 5 * 2 ^ 971 := by
  have hl := log_huge (m := 0x1754d9278b51a7) (by norm_num)
    (239087156439840455083219050173 / 2 ^ 99) (478174312879680910166438100349 / 2 ^ 100)
    (le_log _ _ 40 (by norm_num) (by decide +kernel) (by decide +kernel))
    (log_le _ _ 40 (by norm_num) (by decide +kernel) (by norm_num) (by decide +kernel))
  have hx : (16 : ℝ) ≤ ((0x1754d9278b51a7 * 2 ^ 962 : ℚ) : ℝ) := by norm_num
  obtain ⟨h1, h2⟩ := lgamma_between hx hl.1 hl.2
  have hc : (2 ^ 1024 - 2 ^ 971 - 1 / 5 * 2 ^ 971 : ℚ) ≤
      (0x1754d9278b51a7 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Lo + 239087156439840455083219050173 / 2 ^ 99) -
        0x1754d9278b51a7 * 2 ^ 962 - 2 ∧
      (0x1754d9278b51a7 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Hi + 478174312879680910166438100349 / 2 ^ 100) -
        0x1754d9278b51a7 * 2 ^ 962 + 5 ≤ (2 ^ 1024 - 2 ^ 971 + 1 / 5 * 2 ^ 971 : ℚ) := by
    decide +kernel
  have hc1 := hc.1
  have hc2 := hc.2
  have r1 : ((2 ^ 1024 - 2 ^ 971 - 1 / 5 * 2 ^ 971 : ℚ) : ℝ) ≤ ((
      (0x1754d9278b51a7 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Lo + 239087156439840455083219050173 / 2 ^ 99) -
        0x1754d9278b51a7 * 2 ^ 962 - 2 : ℚ) : ℝ) := by exact_mod_cast hc1
  have r2 : (((0x1754d9278b51a7 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Hi + 478174312879680910166438100349 / 2 ^ 100) -
        0x1754d9278b51a7 * 2 ^ 962 + 5 : ℚ) : ℝ) ≤
      ((2 ^ 1024 - 2 ^ 971 + 1 / 5 * 2 ^ 971 : ℚ) : ℝ) := by exact_mod_cast hc2
  push_cast at r1 r2 h1 h2
  rw [x2, abs_le]
  push_cast
  constructor <;> linarith

/-- `lgamma x ≥ 2 ^ 1024 - 2 ^ 970` from `lgamma`'s overflow threshold on. -/
theorem lgamma_overflow {x : ℝ} (hx : (x3 : ℝ) ≤ x) : 2 ^ 1024 - 2 ^ 970 ≤ lgamma x := by
  have hl := log_huge (m := 0x1754d9278b51a8) (by norm_num)
    (478174312879681103193525762375 / 2 ^ 100) (239087156439840551596762881189 / 2 ^ 99)
    (le_log _ _ 40 (by norm_num) (by decide +kernel) (by decide +kernel))
    (log_le _ _ 40 (by norm_num) (by decide +kernel) (by norm_num) (by decide +kernel))
  have hx16 : (16 : ℝ) ≤ ((0x1754d9278b51a8 * 2 ^ 962 : ℚ) : ℝ) := by norm_num
  obtain ⟨h1, -⟩ := lgamma_between hx16 hl.1 hl.2
  have hc : (2 ^ 1024 - 2 ^ 970 : ℚ) ≤
      (0x1754d9278b51a8 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Lo + 478174312879681103193525762375 / 2 ^ 100) -
        0x1754d9278b51a8 * 2 ^ 962 - 2 := by
    decide +kernel
  have r1 : ((2 ^ 1024 - 2 ^ 970 : ℚ) : ℝ) ≤ ((
      (0x1754d9278b51a8 * 2 ^ 962 - 1 / 2) *
        (1014 * log2Lo + 478174312879681103193525762375 / 2 ^ 100) -
        0x1754d9278b51a8 * 2 ^ 962 - 2 : ℚ) : ℝ) := by exact_mod_cast hc
  have hx' : ((0x1754d9278b51a8 * 2 ^ 962 : ℚ) : ℝ) ≤ x := hx
  have hmono := lgamma_mono (a := ((0x1754d9278b51a8 * 2 ^ 962 : ℚ) : ℝ)) (b := x)
    (by norm_num) hx'
  push_cast at r1 h1 hmono
  exact r1.trans (h1.trans hmono)

#print axioms lgamma_mono
#print axioms lgamma_between
#print axioms gamma_overflow
#print axioms t0_word
#print axioms lgamma_x1
#print axioms lgamma_x2
#print axioms lgamma_overflow
#print axioms x1_word
#print axioms x2_word
#print axioms x3_word

end LeanExe.ProofKit.GammaThresholds
