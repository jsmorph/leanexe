import Project.ProofKit.F64ArithmeticBounds
import Project.ProofKit.RealAffineError

namespace Project.ProofKit.F64AffineUpdate
open CodeLib.IEEE64
open F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem difference_update (ratio state fluxL fluxR : UInt64)
    (hr : Finite ratio) (hs : Finite state) (hl : Finite fluxL) (hh : Finite fluxR)
    (hr0 : 0 ≤ value ratio) (hr1 : value ratio ≤ 1)
    (S D : ℝ) (hS : 1 ≤ S) (hD : 1 ≤ D) (hmax : S + D ≤ (2 : ℝ)^1000)
    (bs : |value state| ≤ S) (bd : |value fluxR - value fluxL| ≤ D) :
    let difference := Wasm.IEEE64.sub fluxR fluxL
    let product := Wasm.IEEE64.mul ratio difference
    let result := Wasm.IEEE64.sub state product
    Finite difference ∧ Finite product ∧ Finite result ∧
    |value result - (value state - value ratio * (value fluxR - value fluxL))| ≤
      arithmeticEpsilon * S + 3 * arithmeticEpsilon * value ratio * D +
        2 * multiplicationUnderflowEpsilon := by
  let difference := Wasm.IEEE64.sub fluxR fluxL
  let product := Wasm.IEEE64.mul ratio difference
  let result := Wasm.IEEE64.sub state product
  have hu0 : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have huHalf : unitRoundoff64 ≤ (1 : ℝ) / 2 := by norm_num [unitRoundoff64]
  have hu1 : unitRoundoff64 ≤ 1 := by linarith only [huHalf]
  have heta : 0 ≤ multiplicationUnderflowEpsilon ∧ multiplicationUnderflowEpsilon ≤ 1 := by
    constructor <;> norm_num [multiplicationUnderflowEpsilon]
  have heps : arithmeticEpsilon = 2 * unitRoundoff64 := by
    norm_num [arithmeticEpsilon, unitRoundoff64]
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hlambdaD := mul_le_mul_of_nonneg_right hr1 hDpos.le
  have hdMax : |value fluxR - value fluxL| < (2 : ℝ)^1023 := by
    have hb : (2 : ℝ)^1000 < (2 : ℝ)^1023 := by norm_num
    linarith only [bd, hmax, hS, hb]
  obtain ⟨hdf, ed⟩ := F64AddBounds.sub_real_relative fluxR fluxL hh hl hdMax
  have edBound : |value difference - (value fluxR - value fluxL)| ≤ unitRoundoff64 * D :=
    ed.trans (mul_le_mul_of_nonneg_left bd hu0)
  have bdRounded : |value difference| ≤ 2 * D := by
    have hb := magnitude_of_error _ _ _ _ edBound bd
    have he := mul_le_mul_of_nonneg_right hu1 hDpos.le
    linarith only [hb, he]
  have bp : |value ratio * value difference| ≤ 2 * value ratio * D := by
    rw [abs_mul, abs_of_nonneg hr0]
    have h := mul_le_mul_of_nonneg_left bdRounded hr0
    nlinarith only [h]
  have hpMax : |value ratio * value difference| < (2 : ℝ)^1022 := by
    have hb : 2 * (2 : ℝ)^1000 < (2 : ℝ)^1022 := by norm_num
    linarith only [bp, hlambdaD, hmax, hS, hb]
  obtain ⟨hpf, ep⟩ := F64MulBounds.mul_real_mixed ratio difference hr hdf hpMax
  have epBound : |value product - value ratio * value difference| ≤
      unitRoundoff64 * (2 * value ratio * D) + multiplicationUnderflowEpsilon :=
    ep.trans (add_le_add (mul_le_mul_of_nonneg_left bp hu0) le_rfl)
  have bpRounded : |value product| ≤ 3 * value ratio * D + multiplicationUnderflowEpsilon := by
    have hb := magnitude_of_error _ _ _ _ epBound bp
    have he := mul_le_mul_of_nonneg_right huHalf (mul_nonneg hr0 hDpos.le)
    nlinarith only [hb, he]
  have bresult : |value state - value product| ≤ S + 3 * value ratio * D + multiplicationUnderflowEpsilon := by
    have h := abs_sub (value state) (value product)
    linarith only [h, bs, bpRounded]
  have hresultMax : |value state - value product| < (2 : ℝ)^1023 := by
    have hb : 3 * (2 : ℝ)^1000 + 1 < (2 : ℝ)^1023 := by norm_num
    linarith only [bresult, hlambdaD, hmax, hS, heta.2, hb]
  obtain ⟨hrf, er⟩ := F64AddBounds.sub_real_relative state product hs hpf hresultMax
  have erBound : |value result - (value state - value product)| ≤
      unitRoundoff64 * (S + 3 * value ratio * D + multiplicationUnderflowEpsilon) :=
    er.trans (mul_le_mul_of_nonneg_left bresult hu0)
  refine ⟨hdf, hpf, hrf, ?_⟩
  have eall := RealAffineError.subtract_product _ _ _ _ _ _ _ _ _ hr0 edBound epBound erBound
  have huS := mul_le_mul_of_nonneg_right hu0 (by linarith only [hS] : 0 ≤ S)
  have huEta := mul_le_mul_of_nonneg_right hu1 heta.1
  apply eall.trans
  rw [heps]
  nlinarith only [huS, huEta]

#print axioms difference_update
end Project.ProofKit.F64AffineUpdate
