import Project.EulerRiemann.NumericsSound

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds

theorem sound_reference_lower (pressure rho : UInt64) (hp : Finite pressure) (hr : Finite rho)
    (reference M : ℝ) (href : 0 < reference) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (brMax : value rho ≤ M)
    (bp : arithmeticEpsilon / 8 ≤ value pressure) (bpMax : value pressure ≤ 5 * M^3)
    (bpRef : (99 / 500) * reference ≤ value pressure) :
    let sound := Wasm.IEEE64.sqrt (Wasm.IEEE64.mul 0x3FF6666666666666 (Wasm.IEEE64.div pressure rho))
    (2 / 3) * Real.sqrt ((14 / 25) * (reference / value rho)) ≤ value sound := by
  let sound := Wasm.IEEE64.sqrt (Wasm.IEEE64.mul 0x3FF6666666666666 (Wasm.IEEE64.div pressure rho))
  let P := value pressure / value rho
  let Q := reference / value rho
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hrPos : 0 < value rho := lt_of_lt_of_le (by positivity) br
  have hpPos : 0 < value pressure := lt_of_lt_of_le (div_pos epsilon_pos (by norm_num)) bp
  have hPpos : 0 < P := div_pos hpPos hrPos
  have hQpos : 0 < Q := div_pos href hrPos
  have hPQ : (99 / 500) * Q ≤ P := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right bpRef hrPos.le
  have hrad : (49 / 100) * ((14 / 25) * Q) ≤ (7 / 5) * P := by
    linarith only [hPQ, hQpos]
  have hrootP := Real.sqrt_nonneg ((7 / 5) * P)
  have hrootQ := Real.sqrt_nonneg ((14 / 25) * Q)
  have hsquareP := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 5) hPpos.le)
  have hsquareQ := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 14 / 25) hQpos.le)
  have hrootLower : (7 / 10) * Real.sqrt ((14 / 25) * Q) ≤ Real.sqrt ((7 / 5) * P) := by
    nlinarith only [hsquareP, hsquareQ, hrootP, hrootQ, hrad]
  obtain ⟨_, _, _, _, herr⟩ := sound_error pressure rho hp hr M hM hMmax br brMax bp bpMax
  have hlo := (abs_le.mp herr).1
  change -(9 * arithmeticEpsilon * Real.sqrt ((7 / 5) * P)) ≤
    value sound - Real.sqrt ((7 / 5) * P) at hlo
  have heps : arithmeticEpsilon ≤ (1 : ℝ) / 1000 := by norm_num [arithmeticEpsilon]
  have hb := mul_le_mul_of_nonneg_right heps hrootP
  change (2 / 3) * Real.sqrt ((14 / 25) * Q) ≤ value sound
  linarith only [hlo, hb, hrootLower, hrootQ]

theorem sound_reference_upper (pressure rho : UInt64) (hp : Finite pressure) (hr : Finite rho)
    (reference M : ℝ) (href : 0 < reference) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (brMax : value rho ≤ M)
    (bp : arithmeticEpsilon / 8 ≤ value pressure) (bpMax : value pressure ≤ 5 * M^3)
    (bpRef : value pressure ≤ (3 / 4) * reference) :
    let sound := Wasm.IEEE64.sqrt (Wasm.IEEE64.mul 0x3FF6666666666666 (Wasm.IEEE64.div pressure rho))
    value sound ≤ 2 * Real.sqrt ((14 / 25) * (reference / value rho)) := by
  let sound := Wasm.IEEE64.sqrt (Wasm.IEEE64.mul 0x3FF6666666666666 (Wasm.IEEE64.div pressure rho))
  let P := value pressure / value rho
  let Q := reference / value rho
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hrPos : 0 < value rho := lt_of_lt_of_le (by positivity) br
  have hpPos : 0 < value pressure := lt_of_lt_of_le (div_pos epsilon_pos (by norm_num)) bp
  have hPpos : 0 < P := div_pos hpPos hrPos
  have hQpos : 0 < Q := div_pos href hrPos
  have hPQ : P ≤ (3 / 4) * Q := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right bpRef hrPos.le
  have hrad : (7 / 5) * P ≤ (9 / 4) * ((14 / 25) * Q) := by
    linarith only [hPQ, hQpos]
  have hrootP := Real.sqrt_nonneg ((7 / 5) * P)
  have hrootQ := Real.sqrt_nonneg ((14 / 25) * Q)
  have hsquareP := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 5) hPpos.le)
  have hsquareQ := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 14 / 25) hQpos.le)
  have hrootUpper : Real.sqrt ((7 / 5) * P) ≤ (3 / 2) * Real.sqrt ((14 / 25) * Q) := by
    nlinarith only [hsquareP, hsquareQ, hrootP, hrootQ, hrad]
  obtain ⟨_, _, _, _, herr⟩ := sound_error pressure rho hp hr M hM hMmax br brMax bp bpMax
  have hhi := (abs_le.mp herr).2
  change value sound - Real.sqrt ((7 / 5) * P) ≤
    9 * arithmeticEpsilon * Real.sqrt ((7 / 5) * P) at hhi
  have heps : arithmeticEpsilon ≤ (1 : ℝ) / 1000 := by norm_num [arithmeticEpsilon]
  have hb := mul_le_mul_of_nonneg_right heps hrootP
  change value sound ≤ 2 * Real.sqrt ((14 / 25) * Q)
  linarith only [hhi, hb, hrootUpper, hrootQ]

#print axioms sound_reference_lower
#print axioms sound_reference_upper
end Project.EulerRiemann.Numerics
