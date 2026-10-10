import Verified.Examples.ExpReductionBounds
import LeanExe.ProofKit.F64MulBounds

namespace Verified.Examples.ExpHighPartBounds
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

private def highPart : ℚ :=
  (Wasm.IEEE64.scaledValue 0x3F762E42FEFA0000 : ℚ) / (2 : ℚ) ^ 1074

theorem high_bias :
    0 < value 0x3F762E42FEFA0000 ∧
    (1 + unitRoundoff64) * value 0x40671547652B82FE * value 0x3F762E42FEFA0000 ≤
      1 - 1 / (2 : ℝ) ^ 40 := by
  have hp : 0 < highPart := by decide +kernel
  have hb : (1 + 1 / (2 : ℚ) ^ 53) * ExpReductionBounds.inverseLogTwo128 * highPart ≤
      1 - 1 / (2 : ℚ) ^ 40 := by decide +kernel
  have hv : (highPart : ℝ) = value 0x3F762E42FEFA0000 := by simp [highPart, value]
  have hpr : 0 < (highPart : ℝ) := by exact_mod_cast hp
  have hbr :
      (((1 + 1 / (2 : ℚ) ^ 53) * ExpReductionBounds.inverseLogTwo128 * highPart : ℚ) : ℝ) ≤
        ((1 - 1 / (2 : ℚ) ^ 40 : ℚ) : ℝ) := Rat.cast_le.mpr hb
  rw [hv] at hpr
  refine ⟨hpr, ?_⟩
  simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_sub, ExpReductionBounds.inverse_value_cast, hv,
    unitRoundoff64] using hbr

private theorem high_residual_nonneg (x : ℝ) (k : Int) (hx : 0 ≤ x)
    (hk : |(k : ℝ) - value 0x40671547652B82FE * x| ≤
      1 / 2 + unitRoundoff64 * |value 0x40671547652B82FE * x| +
        multiplicationUnderflowEpsilon) :
    |x - (k : ℝ) * value 0x3F762E42FEFA0000| ≤ |x| := by
  let inv := value 0x40671547652B82FE
  let H := value 0x3F762E42FEFA0000
  let eta := 1 / (2 : ℝ) ^ 40
  let A := (1 + unitRoundoff64) * inv
  have hi : 0 < inv := ExpReductionBounds.inverse_bounds.1
  have hH : 0 < H := high_bias.1
  have hA : 0 < A := mul_pos (by norm_num [unitRoundoff64]) hi
  have hP : 0 ≤ inv * x := mul_nonneg hi.le hx
  rw [abs_of_nonneg hP] at hk
  have hkn : (0 : Int) ≤ k := by
    by_contra hn
    have hki : k ≤ -1 := by omega
    have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hki
    have habs : (k : ℝ) - inv * x ≤ 0 := by linarith only [hkr, hP]
    rw [abs_of_nonpos habs] at hk
    have huP : unitRoundoff64 * (inv * x) ≤ inv * x :=
      by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by norm_num [unitRoundoff64] : unitRoundoff64 ≤ 1) hP
    have he : multiplicationUnderflowEpsilon < (1 / 2 : ℝ) := by
      norm_num [multiplicationUnderflowEpsilon]
    linarith only [hk, hkr, huP, he]
  have hknr : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkn
  have hupper : (k : ℝ) ≤ A * x + 1 / 2 + multiplicationUnderflowEpsilon := by
    have h := (abs_le.mp hk).2
    dsimp [A]
    nlinarith only [h]
  have hy0 : 0 ≤ (k : ℝ) * H := mul_nonneg hknr hH.le
  have hy2 : (k : ℝ) * H ≤ 2 * x := by
    by_cases hk0 : k = 0
    · simp only [hk0, Int.cast_zero, zero_mul]
      positivity
    · have hki : (1 : Int) ≤ k := by omega
      have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hki
      have hb : A * H ≤ 1 - eta := high_bias.2
      have hbeta : multiplicationUnderflowEpsilon < eta / 2 := by
        norm_num [multiplicationUnderflowEpsilon, eta]
      by_contra h
      have hxy : 2 * x < (k : ℝ) * H := lt_of_not_ge h
      have hAx : 2 * (A * x) < (k : ℝ) * (A * H) := by
        have hscaled := mul_lt_mul_of_pos_left hxy hA
        nlinarith only [hscaled]
      have hAx' : 2 * (A * x) < (k : ℝ) * (1 - eta) :=
        hAx.trans_le (mul_le_mul_of_nonneg_left hb hknr)
      have hkl : 1 + eta ≤ (k : ℝ) * (1 + eta) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hkr (by positivity : 0 ≤ 1 + eta)
      dsimp [eta] at hAx' hkl hbeta
      nlinarith only [hupper, hAx', hkl, hbeta]
  rw [abs_of_nonneg hx]
  apply abs_le.mpr
  constructor <;> linarith only [hy0, hy2]

theorem high_residual_relative (x : ℝ) (k : Int)
    (hk : |(k : ℝ) - value 0x40671547652B82FE * x| ≤
      1 / 2 + unitRoundoff64 * |value 0x40671547652B82FE * x| +
        multiplicationUnderflowEpsilon) :
    |x - (k : ℝ) * value 0x3F762E42FEFA0000| ≤ |x| := by
  by_cases hx : 0 ≤ x
  · exact high_residual_nonneg x k hx hk
  · have hx' : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
    have hk' : |((-k : Int) : ℝ) - value 0x40671547652B82FE * (-x)| ≤
        1 / 2 + unitRoundoff64 * |value 0x40671547652B82FE * (-x)| +
          multiplicationUnderflowEpsilon := by
      have hid : ((-k : Int) : ℝ) - value 0x40671547652B82FE * (-x) =
          -((k : ℝ) - value 0x40671547652B82FE * x) := by
        rw [Int.cast_neg]
        ring
      rw [hid, mul_neg, abs_neg, abs_neg]
      exact hk
    have hp := high_residual_nonneg (-x) (-k) hx' hk'
    have hid : (-x) - ((-k : Int) : ℝ) * value 0x3F762E42FEFA0000 =
        -(x - (k : ℝ) * value 0x3F762E42FEFA0000) := by
      rw [Int.cast_neg]
      ring
    simpa only [hid, abs_neg] using hp

#print axioms high_bias
#print axioms high_residual_relative

end Verified.Examples.ExpHighPartBounds
