import LeanExe.ProofKit.GammaThresholds

/-!
`Γ` at the double before `tgamma`'s overflow threshold `0x1.573fae561f648p+7`
(`GammaThresholds.t0`) lies below `2 ^ 1024 (1 - 2 ^ -50)` (`gamma_below_t0`).  As in
`GammaThresholds.lgamma_t0`, Stirling's series with twelve terms and its remainder bound
`lgamma` at the point, here from above with an upper bound on `log (tp/128)`, and the bound
`lgamma tp ≤ 1024 log 2 - 2 ^ -49` gives the statement through `exp (-u) ≤ 1/(1 + u)`.
An evaluation in 90-digit arithmetic gives `Γ tp = 2 ^ 1024 (1 - 4.79 · 10 ^ -14)`.
-/

namespace LeanExe.ProofKit.GammaBelowT0

open Real PolyBound GammaBasic GammaStirling RatExpLog GammaThresholds

set_option exponentiation.threshold 4096

/-- `0x1.573fae561f647p+7`, the double before `t0`. -/
def tp : ℚ := 0x1573fae561f647 / 2 ^ 45

theorem tp_word : ratOfWord 0x406573FAE561F647 = tp := by decide +kernel

/-- An upper bound on `log (tp/128)`. -/
def logTpHi : ℚ := 371773994577497367164629430625 / 2 ^ 100

theorem lgamma_tp : lgamma tp ≤ 1024 * log 2 - 1 / 2 ^ 49 := by
  have ht16 : (16 : ℝ) ≤ tp := by norm_num [tp]
  have hst := stirling_twelve ht16
  have hlt : log ((tp / 128 : ℚ) : ℝ) ≤ (logTpHi : ℝ) :=
    log_le (tp / 128) logTpHi 40 (by norm_num) (by decide +kernel) (by norm_num [tp])
      (by decide +kernel)
  have hlog : log (tp : ℝ) = 7 * log 2 + log ((tp / 128 : ℚ) : ℝ) := by
    rw [show (tp : ℝ) = 2 ^ 7 * ((tp / 128 : ℚ) : ℝ) by push_cast; ring,
      log_two_pow_mul 7 (by norm_num [tp])]
    norm_num
  have hS : series stirCoeffs tp = (tp : ℝ)⁻¹ * ((qeval stirCoeffs (tp⁻¹ ^ 2) : ℚ) : ℝ) := by
    rw [series, qeval_cast]
    push_cast
    rfl
  have hcheck : (tp - 1 / 2) * (7 * log2Hi + logTpHi) - tp + (2 * log2Hi + logHalfPiHi) / 2 +
      tp⁻¹ * qeval stirCoeffs (tp⁻¹ ^ 2) + 104001 / (25 * (tp - 1) ^ 25) ≤
      1024 * log2Lo - 1 / 2 ^ 49 := by decide +kernel
  have hcr : (((tp - 1 / 2) * (7 * log2Hi + logTpHi) - tp + (2 * log2Hi + logHalfPiHi) / 2 +
      tp⁻¹ * qeval stirCoeffs (tp⁻¹ ^ 2) + 104001 / (25 * (tp - 1) ^ 25) : ℚ) : ℝ) ≤
      ((1024 * log2Lo - 1 / 2 ^ 49 : ℚ) : ℝ) := by exact_mod_cast hcheck
  push_cast at hcr
  rw [← hS] at hcr
  have hl2 := log_two_lo
  have hl2' := log_two_hi
  have hlp := log_half_pi_hi
  have h12 : (0 : ℝ) < (tp : ℝ) - 1 / 2 := by norm_num [tp]
  have hm : ((tp : ℝ) - 1 / 2) * log (tp : ℝ) ≤ ((tp : ℝ) - 1 / 2) * (7 * log2Hi + logTpHi) := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_left (by linarith) h12.le
  rw [abs_le] at hst
  simp only [lead, log_two_pi] at hst
  linarith

/-- `Γ` at the double before `t0` lies below `2 ^ 1024 (1 - 2 ^ -50)`. -/
theorem gamma_below_t0 :
    Real.Gamma (ratOfWord 0x406573FAE561F647) ≤ 2 ^ 1024 * (1 - 2 ^ (-50 : ℤ)) := by
  rw [tp_word]
  have hpos : 0 < Gamma tp := Gamma_pos_of_pos (by norm_num [tp])
  have hu : (0 : ℝ) < 1 - 2 ^ (-50 : ℤ) := by norm_num
  have he2 := RealExpError.exp_pow_two 1024
  push_cast at he2
  have hsmall : Real.exp (-(1 / 2 ^ 49)) ≤ 1 - 2 ^ (-50 : ℤ) := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hu]
    calc (1 - 2 ^ (-50 : ℤ) : ℝ)⁻¹ ≤ 1 / 2 ^ 49 + 1 := by norm_num
      _ ≤ Real.exp (1 / 2 ^ 49) := Real.add_one_le_exp _
  have h := exp_le_exp.mpr lgamma_tp
  rw [lgamma, exp_log hpos, sub_eq_add_neg, Real.exp_add, he2] at h
  calc Gamma tp ≤ 2 ^ 1024 * Real.exp (-(1 / 2 ^ 49)) := h
    _ ≤ 2 ^ 1024 * (1 - 2 ^ (-50 : ℤ)) := mul_le_mul_of_nonneg_left hsmall (by positivity)

#print axioms lgamma_tp
#print axioms gamma_below_t0

end LeanExe.ProofKit.GammaBelowT0
