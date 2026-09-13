import Project.EulerRiemann.NumericsPressure

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem pressure_reference_error (internal : UInt64) (hi : Finite internal)
    (reference M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (bi : |value internal| ≤ 5 * M^3)
    (ei : |value internal - reference| ≤ 12 * arithmeticEpsilon * M^3)
    (hmargin : 24 * arithmeticEpsilon * M^3 ≤ reference) :
    let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
    Project.ProofKit.F64Order.positiveBits pressure = true ∧
    arithmeticEpsilon / 8 ≤ value pressure ∧ value pressure ≤ 5 * M^3 ∧
    |value pressure - (2 / 5) * reference| ≤ 10 * arithmeticEpsilon * M^3 ∧
    (99 / 500) * reference ≤ value pressure ∧ value pressure ≤ (3 / 4) * reference := by
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have heM : 0 < arithmeticEpsilon * M^3 := mul_pos epsilon_pos (pow_pos hMpos 3)
  have href : 0 < reference := by linarith only [hmargin, heM]
  have hilo := (abs_le.mp ei).1
  have hihi := (abs_le.mp ei).2
  have hiHalf : reference / 2 ≤ value internal := by linarith only [hilo, hmargin]
  have hiMin : arithmeticEpsilon ≤ value internal := by
    have hb := mul_le_mul_of_nonneg_left hM3 epsilon_pos.le
    nlinarith only [hilo, hmargin, hb, heM]
  have hiPos : 0 < value internal := epsilon_pos.trans_le hiMin
  have biUpper : value internal ≤ 5 * M^3 := (le_abs_self _).trans bi
  have hiMax : value internal < (2 : ℝ)^1022 := by
    calc
      _ ≤ 5 * M^3 := biUpper
      _ ≤ 5 * ((2 : ℝ)^100)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 3) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  obtain ⟨hp, hplo, hphi, ep⟩ := pressure_error internal hi hiMin hiMax
  have eplo := (abs_le.mp ep).1
  have ephi := (abs_le.mp ep).2
  have hb := mul_le_mul_of_nonneg_left biUpper epsilon_pos.le
  have heps : arithmeticEpsilon ≤ (1 : ℝ) / 1000 := by norm_num [arithmeticEpsilon]
  have he := mul_le_mul_of_nonneg_right heps hiPos.le
  refine ⟨hp, by linarith only [hiMin, hplo], hphi.trans biUpper, ?_, ?_, ?_⟩
  · apply abs_le.mpr
    constructor <;> nlinarith only [hilo, hihi, eplo, ephi, hb, heM]
  · have hpLower : (399 / 1000) * value internal ≤ value pressure := by
      change -(arithmeticEpsilon * value internal) ≤ value pressure - (2 / 5) * value internal at eplo
      linarith only [eplo, he]
    linarith only [hpLower, hiHalf, href]
  · have hiUpper : value internal ≤ (3 / 2) * reference := by
      linarith only [hihi, hmargin]
    have hpUpper : value pressure ≤ (401 / 1000) * value internal := by
      change value pressure - (2 / 5) * value internal ≤ arithmeticEpsilon * value internal at ephi
      linarith only [ephi, he]
    linarith only [hpUpper, hiUpper, href]

#print axioms pressure_reference_error
end Project.EulerRiemann.Numerics
