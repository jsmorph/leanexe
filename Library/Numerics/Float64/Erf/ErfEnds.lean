import Library.Numerics.Float64.Erf.ErfSmallBase
import LeanExe.ProofKit.F64ExactProduct
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
One step for `erf` on the ranges where `s_erf.c` uses no rational function, for positive
arguments.  Below `2^-28` the code computes `x + efx x`, and below `2^-1015` it computes
`(8 x + efx8 x)/8`, where `efx` is `2/√π - 1` rounded up by about `0.112 u`.  `erf x` lies within
`(2/√π) x³/3` of `(2/√π) x`.  On `[2^-1015, 2^-28)` and `[2^-1022, 2^-1015)` the errors add up to at
most `11/8` units of roundoff relative to `erf x` (`F64RelativeSteps.within_steps_relative`); there
`8 x` is exact and the final division by 8 is exact (`F64DivApprox.div_eight_value`).  Below
`2^-1022` the error is below `3/2 · 2^-1074` (`F64RelativeSteps.within_steps_low`).  From 6 on the
code returns the word of 1, and `erfc 6 < 2^-54` (`erfc_six`).
-/

namespace Library.Numerics.Float64.Erf.ErfEnds
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound RealErf ErfKernelSmall ErfSmallBase

set_option exponentiation.threshold 4096

/-- The value of `efx`. -/
def efxQ : ℚ := ratOfWord 0x3FC06EBA8214DB69

theorem efx_value : value (0x3FC06EBA8214DB69 : UInt64) = (efxQ : ℝ) := by
  rw [efxQ, ratOfWord_cast]

theorem efx8_value : value (0x3FF06EBA8214DB69 : UInt64) = 8 * (efxQ : ℝ) := by
  have h : ratOfWord 0x3FF06EBA8214DB69 = 8 * efxQ := by decide +kernel
  rw [← ratOfWord_cast, h]
  push_cast
  ring

theorem efx_bounds : (0 : ℝ) < efxQ ∧ (efxQ : ℝ) ≤ 13 / 100 := by
  have h1 : (0 : ℚ) < efxQ := by decide +kernel
  have h2 : efxQ ≤ 13 / 100 := by decide +kernel
  constructor
  · exact_mod_cast h1
  · have h := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at h
    exact h

/-- `efx` is `2/√π - 1` rounded up by at most `0.1120 u`. -/
theorem efx_near : 0 ≤ (efxQ : ℝ) - (scale - 1) ∧
    (efxQ : ℝ) - (scale - 1) ≤ 1120 / 10000 * (1 / 2 ^ 53) := by
  have hk := scale_bounds
  have h1 : (333038747416263463344 / 2 ^ 68 : ℚ) - 1 ≤ efxQ := by decide +kernel
  have h2 : efxQ - ((333038747416263463341 / 2 ^ 68 : ℚ) - 1) ≤ 1120 / 10000 * (1 / 2 ^ 53) := by
    decide +kernel
  have h1' := (Rat.cast_le (K := ℝ)).mpr h1
  have h2' := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at h1' h2'
  constructor <;> linarith [hk.1, hk.2]

/-- `|erf x - (2/√π) x| ≤ (2/√π) x³/3` for `x ≥ 0`. -/
theorem erf_linear (x : ℝ) (hx : 0 ≤ x) : |RealErf.erf x - scale * x| ≤ scale * (x ^ 3 / 3) := by
  have h := erf_series 1 x
  rw [erfCoeffs_one] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one, mul_one] at h
  have hf : ((Nat.factorial 1 * (2 * 1 + 1) : ℕ) : ℝ) = 3 := by norm_num [Nat.factorial]
  rw [hf, abs_of_nonneg hx] at h
  simpa using h

/-- `x + efx x` approximates `erf x` within `(1/8 + 0.115) 2^-53 x` plus the cubic term. -/
theorem linear_model (x : ℝ) (hx : 0 ≤ x) :
    |x + (efxQ : ℝ) * x - RealErf.erf x| ≤ 1120 / 10000 * (1 / 2 ^ 53) * x + scale * (x ^ 3 / 3) := by
  have h1 := erf_linear x hx
  have h2 := efx_near
  have heq : x + (efxQ : ℝ) * x - RealErf.erf x = ((efxQ : ℝ) - (scale - 1)) * x - (RealErf.erf x - scale * x) := by
    ring
  rw [heq]
  have h3 : |((efxQ : ℝ) - (scale - 1)) * x| ≤ 1120 / 10000 * (1 / 2 ^ 53) * x := by
    rw [abs_mul, abs_of_nonneg h2.1, abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_right h2.2 hx
  calc |((efxQ : ℝ) - (scale - 1)) * x - (RealErf.erf x - scale * x)|
      ≤ |((efxQ : ℝ) - (scale - 1)) * x| + |RealErf.erf x - scale * x| := abs_sub _ _
    _ ≤ _ := add_le_add h3 h1

/-- `erf x ≥ (2/√π)_lo x (1 - x²/3)` for `x ≥ 0`. -/
theorem erf_ge (x : ℝ) (hx : 0 ≤ x) :
    (333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - x ^ 2 / 3) ≤ RealErf.erf x ∨ 3 < x ^ 2 := by
  by_cases h3 : x ^ 2 ≤ 3
  · left
    have hy := erf_lower x hx
    have hk := scale_bounds.1
    have hf : 0 ≤ 1 - x ^ 2 / 3 := by linarith
    calc (333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - x ^ 2 / 3)
        ≤ scale * x * (1 - x ^ 2 / 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hx) hf
      _ = scale * (x * (1 - x ^ 2 / 3)) := by ring
      _ ≤ RealErf.erf x := hy
  · right
    linarith

theorem efx_finite : Finite (0x3FC06EBA8214DB69 : UInt64) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem efx8_finite : Finite (0x3FF06EBA8214DB69 : UInt64) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem one_finite : Finite (0x3FF0000000000000 : UInt64) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem eight_finite : Finite (0x4020000000000000 : UInt64) := by
  unfold CodeLib.IEEE64.Finite
  decide

/-- One step for `erf x` on `[2^-1015, 2^-28)`. -/
theorem erf_tiny (X : UInt64) (hX : Finite X) (hlo : 1 / 2 ^ 1015 ≤ value X)
    (hhi : value X ≤ 1 / 2 ^ 28) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.add X (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 X)) := by
  set x := value X with hxdef
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hlo
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have he : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := by
    norm_num [multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]
  obtain ⟨he0, he1⟩ := efx_bounds
  have hpb : |value (0x3FC06EBA8214DB69 : UInt64) * x| < (2 : ℝ) ^ 1022 := by
    rw [efx_value, abs_mul, abs_of_pos he0, abs_of_pos hx0]
    have : x ≤ 1 := hhi.trans (by norm_num)
    nlinarith [show (1 : ℝ) < 2 ^ 1022 by norm_num]
  obtain ⟨hpf, hpe⟩ := F64MulBounds.mul_real_mixed _ X efx_finite hX hpb
  rw [← hxdef, efx_value, abs_mul, abs_of_pos he0, abs_of_pos hx0, hu, he] at hpe
  set p := value (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 X)
  have hp1 := (abs_le.mp hpe).1
  have hp2 := (abs_le.mp hpe).2
  have hsb : |x + p| < (2 : ℝ) ^ 1023 := by
    rw [abs_lt]
    constructor <;> nlinarith [show (4 : ℝ) < 2 ^ 1023 by norm_num, show (1 : ℝ) / 2 ^ 28 ≤ 1 by
      norm_num]
  obtain ⟨hcf, hce⟩ := F64AddBounds.add_real_relative X _ hX hpf hsb
  rw [← hxdef, hu] at hce
  have hm := linear_model x hx0.le
  have hk := scale_bounds
  have hx2 : x ^ 2 ≤ 1 / 2 ^ 56 := by
    have : x ^ 2 ≤ (1 / 2 ^ 28) ^ 2 := pow_le_pow_left₀ hx0.le hhi 2
    norm_num at this ⊢
    linarith
  have hylo : (333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 56 / 3) ≤ RealErf.erf x := by
    rcases erf_ge x hx0.le with h | h
    · have hf : (1 - 1 / 2 ^ 56 / 3 : ℝ) ≤ 1 - x ^ 2 / 3 := by linarith
      have := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤
        (333038747416263463341 / 2 ^ 68 : ℝ) * x)
      linarith
    · nlinarith
  have hcubic : scale * (x ^ 3 / 3) ≤ 2 * (1 / 2 ^ 56 / 3) * x := by
    have h1 : x * x ^ 2 ≤ x * (1 / 2 ^ 56) := mul_le_mul_of_nonneg_left hx2 hx0.le
    have h2 : scale ≤ 2 := by
      linarith [hk.2, show (333038747416263463344 / 2 ^ 68 : ℝ) ≤ 2 by norm_num]
    calc scale * (x ^ 3 / 3) = scale * (x * x ^ 2 / 3) := by ring
      _ ≤ 2 * (x * (1 / 2 ^ 56) / 3) :=
          mul_le_mul h2 (div_le_div_of_nonneg_right h1 (by norm_num)) (by positivity) (by norm_num)
      _ = 2 * (1 / 2 ^ 56 / 3) * x := by ring
  have hxp : |x + p| ≤ x * (1 + efxQ * (1 + 1 / 2 ^ 53)) + 1 / 2 ^ 1075 := by
    have hη : (1 : ℝ) / 2 ^ 1075 < x := lt_of_lt_of_le (by norm_num) hlo
    have hq : (0 : ℝ) ≤ efxQ * x * (1 - 1 / 2 ^ 53) := by
      apply mul_nonneg (mul_nonneg he0.le hx0.le)
      norm_num
    rw [abs_of_pos (by linarith)]
    linarith
  have hetax : (1 / 2 ^ 1075 : ℝ) ≤ x * (1 / 2 ^ 60) := by
    have : (1 / 2 ^ 1015 : ℝ) * (1 / 2 ^ 60) ≤ x * (1 / 2 ^ 60) :=
      mul_le_mul_of_nonneg_right hlo (by positivity)
    norm_num at this ⊢
    linarith
  apply F64RelativeSteps.within_steps_relative 1 le_rfl (by norm_num) (RealErf.erf x) _ hcf
  · rw [abs_of_pos (lt_of_lt_of_le (by positivity) hylo)]
    have : (17 / 16) / (2 : ℝ) ^ 1022 ≤ (333038747416263463341 / 2 ^ 68 : ℝ) * x *
        (1 - 1 / 2 ^ 56 / 3) := by
      have h1 : (333038747416263463341 / 2 ^ 68 : ℝ) * (1 / 2 ^ 1015) * (1 - 1 / 2 ^ 56 / 3) ≤
          (333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 56 / 3) := by gcongr
      have h2 : (17 / 16) / (2 : ℝ) ^ 1022 ≤
          (333038747416263463341 / 2 ^ 68 : ℝ) * (1 / 2 ^ 1015) * (1 - 1 / 2 ^ 56 / 3) := by
        norm_num
      linarith
    linarith
  · have hy0 : 0 < RealErf.erf x := lt_of_lt_of_le (by positivity) hylo
    rw [abs_of_pos hy0, hu]
    have htri : |value (Wasm.IEEE64.add X (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 X)) - RealErf.erf x| ≤
        |value (Wasm.IEEE64.add X (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 X)) - (x + p)| +
          |p - (efxQ : ℝ) * x| + |x + (efxQ : ℝ) * x - RealErf.erf x| := by
      have h1 := abs_sub_le (value (Wasm.IEEE64.add X (Wasm.IEEE64.mul 0x3FC06EBA8214DB69 X)))
        (x + p) (RealErf.erf x)
      have h2 : |x + p - RealErf.erf x| ≤ |p - (efxQ : ℝ) * x| + |x + (efxQ : ℝ) * x - RealErf.erf x| := by
        have := abs_add_le (p - (efxQ : ℝ) * x) (x + (efxQ : ℝ) * x - RealErf.erf x)
        have heq : p - (efxQ : ℝ) * x + (x + (efxQ : ℝ) * x - RealErf.erf x) = x + p - RealErf.erf x := by ring
        rw [heq] at this
        exact this
      linarith
    have h1 : 1 / (2 : ℝ) ^ 53 * |x + p| ≤
        1 / 2 ^ 53 * (x * (1 + efxQ * (1 + 1 / 2 ^ 53)) + 1 / 2 ^ 1075) :=
      mul_le_mul_of_nonneg_left hxp (by positivity)
    have hfin : (1 : ℝ) / 2 ^ 53 * (x * (1 + efxQ * (1 + 1 / 2 ^ 53)) + 1 / 2 ^ 1075) +
        (1 / 2 ^ 53 * (efxQ * x) + 1 / 2 ^ 1075) +
        (1120 / 10000 * (1 / 2 ^ 53) * x + 2 * (1 / 2 ^ 56 / 3) * x) ≤
        (1 + 3 / 8) * (1 / 2 ^ 53) *
          ((333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 56 / 3)) := by
      have hq : (1 : ℝ) / 2 ^ 53 * (1 + efxQ * (1 + 1 / 2 ^ 53)) + 1 / 2 ^ 53 * efxQ +
          1120 / 10000 * (1 / 2 ^ 53) + 2 * (1 / 2 ^ 56 / 3) + 2 * (1 / 2 ^ 60) ≤
          (1 + 3 / 8) * (1 / 2 ^ 53) *
            ((333038747416263463341 / 2 ^ 68 : ℝ) * (1 - 1 / 2 ^ 56 / 3)) := by
        have h13 : (efxQ : ℝ) ≤ 13 / 100 := he1
        nlinarith
      nlinarith
    have h3 : (1 + 3 / 8) * (1 / (2 : ℝ) ^ 53) *
        ((333038747416263463341 / 2 ^ 68 : ℝ) * x * (1 - 1 / 2 ^ 56 / 3)) ≤
        ((1 : ℕ) + 3 / 8) * (1 / 2 ^ 53) * RealErf.erf x := by
      push_cast
      exact mul_le_mul_of_nonneg_left hylo (by positivity)
    have hm' : |x + (efxQ : ℝ) * x - RealErf.erf x| ≤ 1120 / 10000 * (1 / 2 ^ 53) * x +
        2 * (1 / 2 ^ 56 / 3) * x := by linarith
    have hpe' : |p - (efxQ : ℝ) * x| ≤ 1 / 2 ^ 53 * (efxQ * x) + 1 / 2 ^ 1075 := by
      have : |p - (efxQ : ℝ) * x| = |p - (efxQ : ℝ) * x| := rfl
      linarith
    linarith

theorem erfc_six : RealErf.erfc 6 ≤ 1 / 2 ^ 54 := by
  have h := erfc_asym 1 (x := 6) (by norm_num)
  simp only [pow_one, neg_mul, one_mul, neg_nonneg, sub_nonpos] at h
  have ha : asym 1 6 = scale / 2 * Real.exp (-6 ^ 2) * (6 : ℝ)⁻¹ := by
    simp [asym, asymSum, asymCoeff]
  rw [ha] at h
  have hk := scale_bounds.2
  have he : Real.exp (-6 ^ 2) ≤ 1 / 2 ^ 51 := by
    have h1 : Real.exp 1 ^ 36 = Real.exp 36 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7182818283 : ℝ) ^ 36 ≤ Real.exp 1 ^ 36 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 36
    have h3 : (2 : ℝ) ^ 51 ≤ 2.7182818283 ^ 36 := by norm_num
    have h4 : Real.exp (-6 ^ 2) = (Real.exp 36)⁻¹ := by rw [← Real.exp_neg]; norm_num
    rw [h4, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith
  have hs0 := scale_pos
  have h5 : scale / 2 * Real.exp (-6 ^ 2) * (6 : ℝ)⁻¹ ≤
      (333038747416263463344 / 2 ^ 68) / 2 * (1 / 2 ^ 51) * 6⁻¹ := by
    gcongr
  have h6 : (333038747416263463344 / 2 ^ 68 : ℝ) / 2 * (1 / 2 ^ 51) * 6⁻¹ ≤ 1 / 2 ^ 54 := by
    norm_num
  linarith

/-- One step for `erf x` from 6 on, where the code returns the word of 1. -/
theorem erf_large (X : UInt64) (hx : 6 ≤ value X) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X)) 0x3FF0000000000000 := by
  have he := (erfc_strictAnti.antitone hx).trans erfc_six
  have hep := erfc_pos (value X)
  have hy : RealErf.erf (value X) = 1 - RealErf.erfc (value X) := by simp [RealErf.erfc]
  apply F64RelativeSteps.within_steps_relative 1 le_rfl (by norm_num) _ _ one_finite
  · rw [hy, abs_of_pos (by linarith [show (1 : ℝ) / 2 ^ 54 < 1 / 2 by norm_num])]
    linarith [show (17 / 16) / (2 : ℝ) ^ 1022 ≤ 1 / 2 by norm_num,
      show (1 : ℝ) / 2 ^ 54 < 1 / 2 by norm_num]
  · rw [one_value, hy, show (1 : ℝ) - (1 - RealErf.erfc (value X)) = RealErf.erfc (value X) by ring,
      abs_of_pos hep, abs_of_pos (show (0 : ℝ) < 1 - RealErf.erfc (value X) by
        linarith [show (1 : ℝ) / 2 ^ 54 < 1 / 2 by norm_num])]
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    rw [hu]
    have h2 : (1 : ℝ) / 2 ^ 54 ≤ ((1 : ℕ) + 3 / 8) * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) := by
      norm_num
    have h3 : ((1 : ℕ) + 3 / 8 : ℝ) * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) ≤
        ((1 : ℕ) + 3 / 8) * (1 / 2 ^ 53) * (1 - RealErf.erfc (value X)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-- `1 - tiny` rounds to 1. -/
theorem one_sub_tiny :
    Wasm.IEEE64.sub 0x3FF0000000000000 0x01A56E1FC2F8F359 = 0x3FF0000000000000 := by
  decide +kernel

#print axioms efx_near
#print axioms linear_model
#print axioms erf_tiny
#print axioms erfc_six
#print axioms erf_large
#print axioms one_sub_tiny

end Library.Numerics.Float64.Erf.ErfEnds
