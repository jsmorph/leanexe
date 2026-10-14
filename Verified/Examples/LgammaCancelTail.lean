import LeanExe.ProofKit.GammaThresholds
import LeanExe.ProofKit.F64Grid
import LeanExe.ProofKit.RatExpLog

/-!
The cancellation of the reflection `lgamma x = log π - log |sin (π x)| - lgamma (1 - x)` at the
non-integer doubles below -17.  Such a double is a multiple of `2 ^ -48`
(`F64Grid.value_mul_pow`), so it lies at least `2 ^ -48` from the nearest integer
(`dist_round_ge`) and `|sin (π x)| ≥ π 2 ^ -48 - (π 2 ^ -48) ^ 3/6` (`abs_sin_ge`).  Then
`-log |sin (π x)| ≤ 48 log 2 - log π + 2 ^ -89`, while
`lgamma (1 - x) ≥ log 17! ≥ 48 log 2 + 0.233`, so `lgamma x < -0.23` and
`lgamma (1 - x) ≤ 2 ^ 32 |lgamma x|` (`cancel_tail`).
-/

namespace Verified.Examples.LgammaCancelTail

open Real LeanExe.ProofKit GammaBasic GammaThresholds F64Grid RatExpLog CodeLib.IEEE64

theorem dist_round_ge (w : UInt64) (h16 : (16 : ℝ) ≤ |value w|) (hni : ∀ n : ℤ, value w ≠ n) :
    1 / 2 ^ 48 ≤ |value w - round (value w)| := by
  obtain ⟨m, hm⟩ := value_mul_pow w (k := 4) (by norm_num) (by norm_num; linarith)
  have hm' : value w * 2 ^ 48 = m := by simpa using hm
  have hne : m - round (value w) * 2 ^ 48 ≠ 0 := by
    intro h0
    apply hni (round (value w))
    have h1 : (m : ℝ) = (round (value w) : ℝ) * 2 ^ 48 := by
      have : ((m - round (value w) * 2 ^ 48 : ℤ) : ℝ) = 0 := by exact_mod_cast h0
      push_cast at this
      linarith
    have h2 : value w * 2 ^ 48 = (round (value w) : ℝ) * 2 ^ 48 := by rw [hm', h1]
    exact mul_right_cancel₀ (by positivity) h2
  have h1 : (1 : ℝ) ≤ |((m - round (value w) * 2 ^ 48 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  have he : value w - round (value w) = ((m - round (value w) * 2 ^ 48 : ℤ) : ℝ) / 2 ^ 48 := by
    push_cast
    rw [← hm']
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 48)]
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr h1

theorem abs_sin_ge (x : ℝ) (hd : 1 / 2 ^ 48 ≤ |x - round x|) :
    π / 2 ^ 48 - (π / 2 ^ 48) ^ 3 / 6 ≤ |Real.sin (π * x)| := by
  have hy := abs_sub_round x
  have hs : Real.sin (π * x) = (-1) ^ (round x) * Real.sin (π * (x - round x)) := by
    rw [← Real.sin_add_int_mul_pi]
    congr 1
    ring
  rw [hs, abs_mul, abs_neg_one_zpow, one_mul]
  have hp := Real.pi_pos
  have hmono : Real.sin (π / 2 ^ 48) ≤ |Real.sin (π * (x - round x))| := by
    rcases le_or_gt 0 (x - round x) with h | h
    · rw [abs_of_nonneg h] at hd hy
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hp.le h) (by nlinarith))]
      apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [div_pos hp (by positivity :
        (0 : ℝ) < 2 ^ 48)]) (by nlinarith)
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hd hp.le
    · rw [abs_of_neg h] at hd hy
      have hneg : Real.sin (π * (x - round x)) ≤ 0 := by
        rw [show π * (x - round x) = -(π * -(x - round x)) by ring, Real.sin_neg]
        exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith))
      rw [abs_of_nonpos hneg, show π * (x - round x) = -(π * -(x - round x)) by ring,
        Real.sin_neg, neg_neg]
      apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [div_pos hp (by positivity :
        (0 : ℝ) < 2 ^ 48)]) (by nlinarith)
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hd hp.le
  have hcube := Real.sin_gt_sub_cube (x := π / 2 ^ 48) (by positivity)
  linarith

/-- The reflection's cancellation is at most `2 ^ 32` at the non-integer doubles below -17. -/
theorem cancel_tail (w : UInt64) (hv : value w < -17) (hni : ∀ n : ℤ, value w ≠ n) :
    |lgamma (1 - value w)| ≤ 2 ^ 32 * |lgamma (value w)| := by
  have hp := Real.pi_pos
  have hp4 := Real.pi_le_four
  have h16 : (16 : ℝ) ≤ |value w| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hs := abs_sin_ge (value w) (dist_round_ge w h16 hni)
  have hu : 0 < 1 - π ^ 2 / (6 * 2 ^ 96) := by nlinarith
  have hs0 : 0 < π / 2 ^ 48 - (π / 2 ^ 48) ^ 3 / 6 := by
    have e : π / 2 ^ 48 - (π / 2 ^ 48) ^ 3 / 6 = π / 2 ^ 48 * (1 - π ^ 2 / (6 * 2 ^ 96)) := by ring
    rw [e]
    positivity
  have hlog := Real.log_le_log hs0 hs
  have e1 : π / 2 ^ 48 - (π / 2 ^ 48) ^ 3 / 6 = π / 2 ^ 48 * (1 - π ^ 2 / (6 * 2 ^ 96)) := by ring
  rw [e1, Real.log_mul (by positivity) hu.ne', Real.log_div Real.pi_ne_zero (by positivity),
    Real.log_pow] at hlog
  have hlu : -(2 / 2 ^ 90) ≤ Real.log (1 - π ^ 2 / (6 * 2 ^ 96)) := by
    have hl := Real.one_sub_inv_le_log_of_pos hu
    have hsmall : π ^ 2 / (6 * 2 ^ 96) ≤ 1 / 2 ^ 92 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hinv : (1 - π ^ 2 / (6 * 2 ^ 96))⁻¹ ≤ 1 + 2 / 2 ^ 90 := by
      rw [inv_eq_one_div, div_le_iff₀ hu]
      nlinarith [hsmall]
    linarith
  have hr := lgamma_reflect hni
  rw [← Real.log_abs (Real.sin (π * value w))] at hr
  have hL : lgamma 18 ≤ lgamma (1 - value w) := lgamma_mono (by norm_num) (by linarith)
  have h18 : lgamma 18 = 48 * Real.log 2 + Real.log (355687428096000 / 281474976710656) := by
    rw [lgamma, show (18 : ℝ) = (17 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial,
      show ((Nat.factorial 17 : ℕ) : ℝ) = 2 ^ 48 * (355687428096000 / 281474976710656) by
        norm_num [Nat.factorial],
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hc1 : ((233 / 1000 : ℚ) : ℝ) ≤ Real.log ((355687428096000 / 281474976710656 : ℚ) : ℝ) :=
    le_log _ _ 20 (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at hc1
  have hl2 : Real.log 2 < 1 := by
    have h2 := log_two_hi
    have h3 : (log2Hi : ℝ) < 1 := by norm_num [log2Hi]
    linarith
  have hneg : lgamma (value w) < 0 := by
    push_cast at hlog
    linarith
  have hnn : 0 ≤ lgamma (1 - value w) := by
    have : (0 : ℝ) ≤ 48 * Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    linarith
  rw [abs_of_nonneg hnn, abs_of_neg hneg]
  push_cast at hlog
  linarith

#print axioms cancel_tail

end Verified.Examples.LgammaCancelTail
