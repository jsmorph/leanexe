import Project.EulerRiemann.NumericsSoundRatio
import Project.EulerRiemann.NumericsRadicand
import Project.ProofKit.F64SqrtComposition

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.ProofKit.F64PositiveArithmetic

set_option exponentiation.threshold 4096

theorem sound_error (pressure rho : UInt64) (hp : Finite pressure) (hr : Finite rho)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (brMax : value rho ≤ M)
    (bp : arithmeticEpsilon / 8 ≤ value pressure) (bpMax : value pressure ≤ 5 * M^3) :
    let ratio := Wasm.IEEE64.div pressure rho
    let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 ratio
    let sound := Wasm.IEEE64.sqrt radicand
    Project.ProofKit.F64Order.positiveBits ratio = true ∧
    Project.ProofKit.F64Order.positiveBits radicand = true ∧
    Project.ProofKit.F64Order.positiveBits sound = true ∧ value sound ≤ 14 * M^2 ∧
    |value sound - Real.sqrt ((7 / 5) * (value pressure / value rho))| ≤
      9 * arithmeticEpsilon * Real.sqrt ((7 / 5) * (value pressure / value rho)) := by
  let ratio := Wasm.IEEE64.div pressure rho
  let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 ratio
  let sound := Wasm.IEEE64.sqrt radicand
  let Q := value pressure / value rho
  let R := (7 / 5) * Q
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hrPos : 0 < value rho := lt_of_lt_of_le (by positivity) br
  have hpPos : 0 < value pressure := lt_of_lt_of_le (div_pos epsilon_pos (by norm_num)) bp
  have hQpos : 0 < Q := div_pos hpPos hrPos
  have hRpos : 0 < R := mul_pos (by norm_num) hQpos
  obtain ⟨hqPos, hqNormal, hqUpper, eq⟩ := sound_ratio_error pressure rho hp hr M hM hMmax br brMax bp bpMax
  have hqFinite := (positive_input ratio hqPos).1
  have hqMax : value ratio < (2 : ℝ)^1020 := by
    calc
      value ratio ≤ 10 * M^4 := hqUpper
      _ ≤ 10 * ((2 : ℝ)^100)^4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 4) (by norm_num)
      _ < (2 : ℝ)^1020 := by norm_num
  obtain ⟨hradPos, _, hradUpper, erad⟩ := radicand_error ratio hqFinite hqNormal hqMax
  have hqRelative : value ratio ≤ 2 * Q := by
    have hu := (abs_le.mp eq).2
    have hb := mul_le_mul_of_nonneg_right epsilon_small.le hQpos.le
    change value ratio - Q ≤ arithmeticEpsilon * Q at hu
    linarith only [hu, hb, hQpos]
  have hradRelative : |value radicand - R| ≤ (8 * arithmeticEpsilon) * R := by
    have hqlo := (abs_le.mp eq).1
    have hqhi := (abs_le.mp eq).2
    have hrlo := (abs_le.mp erad).1
    have hrhi := (abs_le.mp erad).2
    have hb := mul_le_mul_of_nonneg_left hqRelative epsilon_pos.le
    have he := mul_pos epsilon_pos hQpos
    change -(arithmeticEpsilon * Q) ≤ value ratio - Q at hqlo
    change value ratio - Q ≤ arithmeticEpsilon * Q at hqhi
    change -(3 * arithmeticEpsilon * value ratio) ≤ value radicand - (7 / 5) * value ratio at hrlo
    change value radicand - (7 / 5) * value ratio ≤ 3 * arithmeticEpsilon * value ratio at hrhi
    change |value radicand - (7 / 5) * Q| ≤ (8 * arithmeticEpsilon) * ((7 / 5) * Q)
    apply abs_le.mpr
    constructor <;> linarith only [hqlo, hqhi, hrlo, hrhi, hb, he]
  obtain ⟨hsoundPos, esound⟩ := Project.ProofKit.F64SqrtComposition.input_error radicand
    hradPos R (8 * arithmeticEpsilon) hRpos (by linarith only [epsilon_small]) hradRelative
  have bsound : value sound ≤ 14 * M^2 := by
    obtain ⟨hf, hsign, hz⟩ := positive_input radicand hradPos
    have hu := (sqrt_positive radicand hf hz hsign).2.2
    have hrPos := (Project.ProofKit.F64Order.positiveBits_spec radicand hradPos).2
    have hrootPos := Real.sqrt_nonneg (value radicand)
    have hrootSq := Real.sq_sqrt hrPos.le
    have hM2 : 0 < M^2 := pow_pos hMpos 2
    have hrootUpper : Real.sqrt (value radicand) ≤ 7 * M^2 := by
      change value radicand ≤ 4 * value ratio at hradUpper
      change value ratio ≤ 10 * M^4 at hqUpper
      nlinarith only [hrootSq, hradUpper, hqUpper, hrootPos, hM2]
    change value sound ≤ 2 * Real.sqrt (value radicand) at hu
    linarith only [hu, hrootUpper]
  refine ⟨hqPos, hradPos, hsoundPos, bsound, ?_⟩
  exact esound.trans_eq (by ring)

#print axioms sound_error
end Project.EulerRiemann.Numerics
