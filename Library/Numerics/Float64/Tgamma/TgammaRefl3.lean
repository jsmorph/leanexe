import Library.Numerics.Float64.Tgamma.TgammaRefl2
import LeanExe.ProofKit.F64RelativeSteps

/-!
The word operations of the path of `tgammaWith` below `-3`, and one step for results of any size.
`field_eq` reads the exponent field as the code does, `nonPositive_sub` decides `re - e ≤ 0` for
small fields, `scale_down` subtracts `E` from the exponent field of a normal word of either sign,
`th_value` builds `±2 ^ (E - 1022)` from `rh`, and `mask_value` clears the exponent field of a word
in the binade of `2 ^ (E - 1022)`.  `within_one_abs` gives one step from a relative error of
`9/8` units of roundoff below `2 ^ 1021` without a lower bound, through `F64Approx.within_one_of_error`
on the binade of the result, and `within_low` gives one step from an absolute error below
`3/2 · 2 ^ -1074`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaRefl3
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaFloor

set_option exponentiation.threshold 4096

/-- One step for a positive `y` below `2 ^ 1021` from a relative error of `9/8` units. -/
theorem within_pos (y : ℝ) (c : UInt64) (hcf : Finite c) (hy0 : 0 < y) (hy : y < 2 ^ 1021)
    (hc : |value c - y| ≤ 9 / 8 / 2 ^ 53 * y) : F64SignedRounding.WithinSteps 1 y c := by
  obtain ⟨E, hE⟩ : ∃ E, E = 9 / 8 / 2 ^ 53 * y := ⟨_, rfl⟩
  rw [← hE] at hc
  rcases lt_or_ge (y - E) (1 / 2 ^ 1021) with ht | ht
  · have h0 : value (UInt64.ofNat (0 * 2 ^ 52)) = 0 := by
      rw [TgammaSpecial.lit_value _ 0 (by decide +kernel)]
      norm_num
    apply within_one_of_error y c 0 (by norm_num) E hcf hc (by rw [h0]; linarith)
    · norm_num
      linarith
    · linarith
  · obtain ⟨n, hn2, hn, hBy, hyB⟩ := F64RoundNearest.binade_of_real (y - E) ht (by linarith)
    have hb := F64PositiveSpacing.boundary_value n (by omega) (by omega)
    have hpw : (2 : ℝ) ^ (n + 51) = 2 ^ (n - 1) * 2 ^ 52 := by
      rw [← pow_add]; congr 1; omega
    rw [hb, hpw] at hBy hyB
    apply within_one_of_error y c n (by omega) E hcf hc (by rw [hb, hpw]; linarith) ?_ (by linarith)
    have hP : (0 : ℝ) < 2 ^ (n - 1) / 2 ^ 1074 := by positivity
    rw [show (2 : ℝ) ^ (n - 1) * 2 ^ 52 / 2 ^ 1074 = 2 ^ 52 * (2 ^ (n - 1) / 2 ^ 1074) by ring]
      at hyB
    linarith

/-- **One step** for a nonzero `y` below `2 ^ 1021` from a relative error of `9/8` units. -/
theorem within_one_abs (y : ℝ) (c : UInt64) (hcf : Finite c) (hy0 : y ≠ 0) (hy : |y| < 2 ^ 1021)
    (hc : |value c - y| ≤ 9 / 8 / 2 ^ 53 * |y|) : F64SignedRounding.WithinSteps 1 y c := by
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · apply within_of_negate 1 y c
    obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c hcf
    rw [abs_of_neg hneg] at hy hc
    apply within_pos (-y) _ hnf (by linarith) hy
    rw [hnv, show -value c - -y = -(value c - y) by ring, abs_neg]
    exact hc
  · rw [abs_of_pos hpos] at hy hc
    exact within_pos y c hcf hpos hy hc

/-- **One step** from an absolute error below `3/2 · 2 ^ -1074`, for a result with the sign of
`y`. -/
theorem within_low (y : ℝ) (c : UInt64) (hcf : Finite c)
    (hs : Wasm.IEEE64.sign c = decide (y < 0))
    (he : |value c - y| < 3 / 2 / 2 ^ 1074) : F64SignedRounding.WithinSteps 1 y c := by
  rcases lt_or_ge y 0 with hneg | hpos
  · apply within_of_negate 1 y c
    obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c hcf
    have hns : Wasm.IEEE64.sign (Wasm.IEEE64.negate c) = false := by
      have h := (F64Sign.fields_negate c).2.2
      rw [hs, decide_eq_true hneg] at h
      exact h
    apply F64RelativeSteps.within_steps_low 1 le_rfl (by norm_num) (-y) (by linarith) _ hnf hns
    rw [hnv, show -value c - -y = -(value c - y) by ring, abs_neg]
    push_cast
    linarith
  · rw [decide_eq_false (not_lt.mpr hpos)] at hs
    exact F64RelativeSteps.within_steps_low 1 le_rfl (by norm_num) y hpos c hcf hs
      (by push_cast; linarith)

#print axioms within_one_abs
#print axioms within_low

end Library.Numerics.Float64.Tgamma.TgammaRefl3
