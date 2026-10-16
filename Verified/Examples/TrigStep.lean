import LeanExe.ProofKit.F64UnitStep
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The last step of `sin` and `cos`: a finite word close to `sin r` or `cos r` lies within one step
of the nearest-even reference.  `F64UnitStep.unit_step` covers results from `1/2` to `2` in
magnitude with an error below one and a half spacings of `[1/2, 1)`.  `sin_final` takes the
kernel's bound in powers of `X`, near `|r|`, and applies `F64RelativeStep.within_one_relative` for
`|r| ≤ 0.54` and `unit_step` above, and `cos_final` applies `unit_step`.
-/

namespace Verified.Examples.TrigStep

open CodeLib.IEEE64 LeanExe.ProofKit

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 1200

/-- `|sin r| = sin |r|` for `|r| ≤ π`. -/
theorem abs_sin_eq (r : ℝ) (h : |r| ≤ Real.pi) : |Real.sin r| = Real.sin |r| := by
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr] at h ⊢
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr h)
  · rw [abs_of_neg hr] at h ⊢
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : (0 : ℝ) ≤ -r) h
    rw [Real.sin_neg] at hs ⊢
    exact abs_of_nonpos (by linarith)

/-- A finite word that rounds `t`, with `t` within `u (33/40 X ^ 3 + X / 30)` of `sin a` and `a`
within `|r| / 2 ^ 59` of `r`, lies within one step of the nearest-even reference of `sin r`. -/
theorem sin_final (c : UInt64) (t a r X : ℝ) (hcf : Finite c)
    (hct : |value c - t| ≤ 𝐮 * |t|)
    (hta : |t - Real.sin a| ≤ 𝐮 * (33 / 40 * X ^ 3 + X / 30))
    (har : |a - r| ≤ |r| / 2 ^ 59) (hX0 : 0 ≤ X)
    (hX1 : X ≤ |r| * (1 + 1 / 2 ^ 50))
    (hr0 : 1 / 2 ^ 69 ≤ |r|) (hr1 : |r| ≤ 78541 / 100000) :
    F64SignedRounding.WithinSteps 1 (Real.sin r) c := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  set R := |r| with hR
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hr0
  have hpi : R ≤ Real.pi := hr1.trans (by linarith [Real.pi_gt_three])
  have hsr : |Real.sin r| = Real.sin R := abs_sin_eq r hpi
  have hlo := Real.sin_gt_sub_cube hR0
  have hhi := Real.abs_sin_le_one r
  -- The error of `t` from `sin r`.
  have hsa : |Real.sin a - Real.sin r| ≤ R / 2 ^ 59 :=
    (Real.abs_sin_sub_sin_le a r).trans har
  have hδ : |t - Real.sin r| ≤ 𝐮 * (33 / 40 * X ^ 3 + X / 30) + R / 2 ^ 59 := by
    have h := abs_sub_le t (Real.sin a) (Real.sin r)
    linarith
  set δ := |t - Real.sin r| with hδdef
  have ht : |t| ≤ |Real.sin r| + δ := by
    have h := abs_sub_abs_le_abs_sub t (Real.sin r)
    linarith
  have hc : |value c - Real.sin r| ≤ 𝐮 * (|Real.sin r| + δ) + δ := by
    have h := abs_sub_le (value c) t (Real.sin r)
    have hu0 : 0 ≤ 𝐮 := by rw [hu]; positivity
    have := mul_le_mul_of_nonneg_left ht hu0
    linarith
  have hX3 : X ^ 3 ≤ R ^ 3 * (1 + 1 / 2 ^ 50) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hX0 hX1 3
  rcases le_or_gt R (54 / 100) with hsmall | hlarge
  · -- Relative to `sin r`.
    have hR2 : R ^ 3 ≤ 2916 / 10000 * R := by
      have : R ^ 2 ≤ 2916 / 10000 := by nlinarith
      nlinarith
    refine F64RelativeStep.within_one_relative (Real.sin r) c hcf ?_ ?_
    · rw [hsr]
      have : (1 : ℝ) / 2 ^ 1000 ≤ R - R ^ 3 / 6 := by
        have h69 : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 70 := by norm_num
        nlinarith
      linarith
    · rw [hsr] at hc ⊢
      rw [hu] at hc hδ ⊢
      norm_num [unitRoundoff64] at hc hδ hX3 ⊢
      nlinarith
  · -- Within one and a half spacings of `[1/2, 1)`.
    have hs : 1 / 2 + 1 / 2 ^ 50 ≤ |Real.sin r| := by
      rw [hsr]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ R - 54 / 100)
        (by nlinarith : (0 : ℝ) ≤ 6 - R ^ 2 - 54 / 100 * R - 2916 / 10000)]
    refine F64UnitStep.unit_step (Real.sin r) c hcf hs hhi ?_
    have hR3 : R ^ 3 ≤ 4846 / 10000 := by
      have : R ^ 3 ≤ (78541 / 100000) ^ 3 := pow_le_pow_left₀ hR0.le hr1 3
      linarith [show ((78541 : ℝ) / 100000) ^ 3 ≤ 4845 / 10000 by norm_num]
    rw [hu] at hc hδ
    norm_num [unitRoundoff64] at hc hδ hX3 ⊢
    nlinarith

/-- A finite word within `7/5 u` of `cos a`, with `a` within `|r| / 2 ^ 59` of `r`, lies within one
step of the nearest-even reference of `cos r`. -/
theorem cos_final (c : UInt64) (a r : ℝ) (hcf : Finite c)
    (hca : |value c - Real.cos a| ≤ 7 / 5 * 𝐮)
    (har : |a - r| ≤ |r| / 2 ^ 59) (hr1 : |r| ≤ 78541 / 100000) :
    F64SignedRounding.WithinSteps 1 (Real.cos r) c := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hcos := Real.one_sub_sq_div_two_le_cos (x := r)
  have hr2 : r ^ 2 ≤ 617 / 1000 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg r]
  have hcl : 1 / 2 + 1 / 2 ^ 50 ≤ |Real.cos r| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hsc : |Real.cos a - Real.cos r| ≤ |r| / 2 ^ 59 :=
    (Real.abs_cos_sub_cos_le a r).trans har
  refine F64UnitStep.unit_step (Real.cos r) c hcf hcl (Real.abs_cos_le_one r) ?_
  have h := abs_sub_le (value c) (Real.cos a) (Real.cos r)
  rw [hu] at hca
  have : |r| / 2 ^ 59 ≤ 1 / 2 ^ 59 := by
    have : |r| ≤ 1 := hr1.trans (by norm_num)
    exact div_le_div_of_nonneg_right this (by positivity)
  norm_num at hca this ⊢
  linarith

#print axioms sin_final
#print axioms cos_final

end Verified.Examples.TrigStep
