import Project.EulerRiemann.NumericsConstants
import Project.ProofKit.F64PositiveArithmetic

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.ProofKit.F64PositiveArithmetic

set_option exponentiation.threshold 4096

theorem pressure_error (internal : UInt64) (hi : Finite internal)
    (hmin : arithmeticEpsilon ≤ value internal) (hmax : value internal < (2 : ℝ)^1022) :
    let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
    Project.ProofKit.F64Order.positiveBits pressure = true ∧
    value internal / 8 ≤ value pressure ∧ value pressure ≤ value internal ∧
    |value pressure - (2 / 5) * value internal| ≤ arithmeticEpsilon * value internal := by
  have hiPos : 0 < value internal := epsilon_pos.trans_le hmin
  have hcoeff : (2 : ℝ) / 5 ≤ value 0x3FD999999999999A ∧
      value 0x3FD999999999999A ≤ 1 / 2 := by
    rw [pressure_factor_value]
    constructor <;> linarith only [epsilon_pos, epsilon_small]
  have hprodMin : minNormal64 ≤ value 0x3FD999999999999A * value internal := by
    calc
      minNormal64 ≤ (2 / 5) * arithmeticEpsilon := by norm_num [minNormal64, arithmeticEpsilon]
      _ ≤ value 0x3FD999999999999A * value internal :=
        mul_le_mul hcoeff.1 hmin epsilon_pos.le (by linarith only [hcoeff.1])
  have hprodMax : value 0x3FD999999999999A * value internal < (2 : ℝ)^1022 := by
    have h := mul_le_mul_of_nonneg_right hcoeff.2 hiPos.le
    linarith only [h, hmax, hiPos]
  obtain ⟨hf, hl, hu⟩ := mul_positive _ internal pressure_factor_finite hi hprodMin hprodMax
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  have hlo : value internal / 8 ≤ value pressure := by
    have h := mul_le_mul_of_nonneg_right hcoeff.1 hiPos.le
    change value 0x3FD999999999999A * value internal / 2 ≤ value pressure at hl
    linarith only [hl, h, hiPos]
  have hhi : value pressure ≤ value internal := by
    have h := mul_le_mul_of_nonneg_right hcoeff.2 hiPos.le
    change value pressure ≤ 2 * (value 0x3FD999999999999A * value internal) at hu
    linarith only [hu, h]
  have hpos := Project.ProofKit.F64Order.positiveBits_of_finite_value_pos _ hf
    (lt_of_lt_of_le (by positivity : 0 < value internal / 8) hlo)
  refine ⟨hpos, hlo, hhi, ?_⟩
  have hp : 0 < value 0x3FD999999999999A * value internal := by
    have h : 0 < value 0x3FD999999999999A := by linarith only [hcoeff.1]
    exact mul_pos h hiPos
  have he := Project.ProofKit.F64MulBounds.mul_real_mixed _ internal pressure_factor_finite hi
    (by rwa [abs_of_pos hp])
  rw [abs_of_pos hp] at he
  have hrelative := normal_relative _ _ hprodMin he.2
  have hround : |value pressure - value 0x3FD999999999999A * value internal| ≤
      arithmeticEpsilon * value internal / 2 := by
    refine hrelative.trans ?_
    have h := mul_le_mul_of_nonneg_left hcoeff.2 (mul_nonneg epsilon_pos.le hiPos.le)
    nlinarith only [h]
  have hcoefficientError : value 0x3FD999999999999A * value internal - (2 / 5) * value internal =
      arithmeticEpsilon * value internal / 10 := by rw [pressure_factor_value]; ring
  calc
    |value pressure - (2 / 5) * value internal| =
        |(value pressure - value 0x3FD999999999999A * value internal) +
          (value 0x3FD999999999999A * value internal - (2 / 5) * value internal)| := by congr 1; ring
    _ ≤ |value pressure - value 0x3FD999999999999A * value internal| +
        |value 0x3FD999999999999A * value internal - (2 / 5) * value internal| := abs_add_le _ _
    _ ≤ arithmeticEpsilon * value internal / 2 + arithmeticEpsilon * value internal / 10 :=
      add_le_add hround (by rw [hcoefficientError, abs_of_nonneg
        (div_nonneg (mul_nonneg epsilon_pos.le hiPos.le) (by norm_num))])
    _ ≤ arithmeticEpsilon * value internal := by
      nlinarith only [mul_pos epsilon_pos hiPos]

#print axioms pressure_error
end Project.EulerRiemann.Numerics
