import Project.EulerRiemann.NumericsConstants
import Project.ProofKit.F64PositiveArithmetic

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.ProofKit.F64PositiveArithmetic

set_option exponentiation.threshold 4096

theorem radicand_error (ratio : UInt64) (hq : Finite ratio)
    (hmin : minNormal64 ≤ value ratio) (hmax : value ratio < (2 : ℝ)^1020) :
    let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 ratio
    Project.ProofKit.F64Order.positiveBits radicand = true ∧
    value ratio / 2 ≤ value radicand ∧ value radicand ≤ 4 * value ratio ∧
    |value radicand - (7 / 5) * value ratio| ≤ 3 * arithmeticEpsilon * value ratio := by
  have hqPos : 0 < value ratio := lt_of_lt_of_le (by norm_num [minNormal64]) hmin
  have hcoeff : 1 ≤ value 0x3FF6666666666666 ∧ value 0x3FF6666666666666 ≤ 2 := by
    rw [sound_factor_value]
    constructor <;> linarith only [epsilon_pos, epsilon_small]
  have hprodMin : minNormal64 ≤ value 0x3FF6666666666666 * value ratio :=
    hmin.trans (by nlinarith only [mul_le_mul_of_nonneg_right hcoeff.1 hqPos.le])
  have hprodMax : value 0x3FF6666666666666 * value ratio < (2 : ℝ)^1022 := by
    have h := mul_le_mul_of_nonneg_right hcoeff.2 hqPos.le
    have hb : (2 : ℝ) * (2 : ℝ)^1020 < (2 : ℝ)^1022 := by norm_num
    linarith only [h, hmax, hb]
  obtain ⟨hf, hl, hu⟩ := mul_positive _ ratio sound_factor_finite hq hprodMin hprodMax
  let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 ratio
  have hlo : value ratio / 2 ≤ value radicand := by
    have h := mul_le_mul_of_nonneg_right hcoeff.1 hqPos.le
    change value 0x3FF6666666666666 * value ratio / 2 ≤ value radicand at hl
    linarith only [hl, h]
  have hhi : value radicand ≤ 4 * value ratio := by
    have h := mul_le_mul_of_nonneg_right hcoeff.2 hqPos.le
    change value radicand ≤ 2 * (value 0x3FF6666666666666 * value ratio) at hu
    linarith only [hu, h]
  have hpos := Project.ProofKit.F64Order.positiveBits_of_finite_value_pos _ hf
    (lt_of_lt_of_le (div_pos hqPos (by norm_num)) hlo)
  refine ⟨hpos, hlo, hhi, ?_⟩
  have hp : 0 < value 0x3FF6666666666666 * value ratio :=
    mul_pos (lt_of_lt_of_le (by norm_num) hcoeff.1) hqPos
  have he := Project.ProofKit.F64MulBounds.mul_real_mixed _ ratio sound_factor_finite hq
    (by rwa [abs_of_pos hp])
  rw [abs_of_pos hp] at he
  have hrelative := normal_relative _ _ hprodMin he.2
  have hround : |value radicand - value 0x3FF6666666666666 * value ratio| ≤
      2 * arithmeticEpsilon * value ratio := by
    refine hrelative.trans ?_
    have h := mul_le_mul_of_nonneg_left hcoeff.2 (mul_nonneg epsilon_pos.le hqPos.le)
    nlinarith only [h]
  have hcoefficientError : value 0x3FF6666666666666 * value ratio - (7 / 5) * value ratio =
      -(2 / 5) * arithmeticEpsilon * value ratio := by rw [sound_factor_value]; ring
  have hl := (abs_le.mp hround).1
  have hu := (abs_le.mp hround).2
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu, hcoefficientError, mul_pos epsilon_pos hqPos]

#print axioms radicand_error
end Project.EulerRiemann.Numerics
