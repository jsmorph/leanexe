import Project.ProofKit.F64PositiveArithmetic

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.ProofKit.F64PositiveArithmetic

set_option exponentiation.threshold 4096

theorem sound_ratio_error (pressure rho : UInt64) (hp : Finite pressure) (hr : Finite rho)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (brMax : value rho ≤ M)
    (bp : arithmeticEpsilon / 8 ≤ value pressure) (bpMax : value pressure ≤ 5 * M^3) :
    let ratio := Wasm.IEEE64.div pressure rho
    Project.ProofKit.F64Order.positiveBits ratio = true ∧
    minNormal64 ≤ value ratio ∧ value ratio ≤ 10 * M^4 ∧
    |value ratio - value pressure / value rho| ≤ arithmeticEpsilon * (value pressure / value rho) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hrPos : 0 < value rho := lt_of_lt_of_le (by positivity) br
  have hpPos : 0 < value pressure := lt_of_lt_of_le (div_pos epsilon_pos (by norm_num)) bp
  have hr0 : Wasm.IEEE64.scaledMagnitude rho ≠ 0 := by
    intro hz
    have hv : value rho = 0 := by simp [value, Wasm.IEEE64.scaledValue, hz]
    linarith only [hv, hrPos]
  have hquotPos : 0 < value pressure / value rho := div_pos hpPos hrPos
  have hquotLower : arithmeticEpsilon / (8 * M) ≤ value pressure / value rho := by
    calc
      arithmeticEpsilon / (8 * M) = (arithmeticEpsilon / 8) / M := by ring
      _ ≤ value pressure / M := div_le_div_of_nonneg_right bp hMpos.le
      _ ≤ value pressure / value rho := div_le_div_of_nonneg_left hpPos.le hrPos brMax
  have hnormalLower : 2 * minNormal64 ≤ arithmeticEpsilon / (8 * M) := by
    calc
      2 * minNormal64 ≤ arithmeticEpsilon / (8 * (2 : ℝ)^100) := by
        norm_num [minNormal64, arithmeticEpsilon]
      _ ≤ arithmeticEpsilon / (8 * M) := div_le_div_of_nonneg_left epsilon_pos.le
        (by positivity) (mul_le_mul_of_nonneg_left hMmax (by norm_num))
  have hquotNormal : minNormal64 ≤ value pressure / value rho := by
    have hm : 0 < minNormal64 := by norm_num [minNormal64]
    linarith only [hnormalLower, hquotLower, hm]
  have hquotUpper : value pressure / value rho ≤ 5 * M^4 := by
    apply (div_le_iff₀ hrPos).2
    have h := mul_le_mul_of_nonneg_left br (by positivity : 0 ≤ 5 * M^4)
    have heq : 5 * M^4 * (1 / M) = 5 * M^3 := by field_simp
    rw [heq] at h
    exact bpMax.trans h
  have hquotMax : value pressure / value rho < (2 : ℝ)^1022 := by
    calc
      value pressure / value rho ≤ 5 * M^4 := hquotUpper
      _ ≤ 5 * ((2 : ℝ)^100)^4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 4) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  obtain ⟨hf, hl, hu⟩ := div_positive pressure rho hp hr hr0 hquotNormal hquotMax
  let ratio := Wasm.IEEE64.div pressure rho
  have hnormal : minNormal64 ≤ value ratio := by
    change (value pressure / value rho) / 2 ≤ value ratio at hl
    linarith only [hl, hquotLower, hnormalLower]
  have hupper : value ratio ≤ 10 * M^4 := by
    change value ratio ≤ 2 * (value pressure / value rho) at hu
    linarith only [hu, hquotUpper]
  have hpos := Project.ProofKit.F64Order.positiveBits_of_finite_value_pos _ hf
    (lt_of_lt_of_le (by norm_num [minNormal64]) hnormal)
  have he := Project.ProofKit.F64DivBounds.div_real_mixed pressure rho hp hr hr0
    (by rwa [abs_of_pos hquotPos])
  rw [abs_of_pos hquotPos] at he
  exact ⟨hpos, hnormal, hupper, normal_relative _ _ hquotNormal he.2⟩

#print axioms sound_ratio_error
end Project.EulerRiemann.Numerics
