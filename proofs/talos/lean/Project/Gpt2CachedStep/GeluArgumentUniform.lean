import Project.Gpt2CachedStep.GeluArgumentError
import Project.ProofKit.F32UniformRange

set_option exponentiation.threshold 512

namespace Project.Gpt2CachedStep.GeluArgumentUniform
open Project.ProofKit CodeLib.IEEE32

def bounds : GeluArgumentError.Bounds := ⟨305, 300, 152, 303, 304⟩

theorem magnitude_bound (a : UInt32) (m : Nat)
    (h : (Wasm.IEEE32.scaledValue a).natAbs ≤ m) : |value a| ≤ (m : ℝ) / 2 ^ 149 := by
  rw [F32Order.abs_value_scaledMagnitude]
  rw [natAbs_scaledValue] at h
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem intermediates (a : UInt32) (ha : CodeLib.IEEE32.Finite a)
    (h : GeluArgumentError.Ranges a bounds) :
    |value (GeluArgumentError.square a)| ≤ 129 ∧ |value (GeluArgumentError.product a)| ≤ 33 := by
  have hs := F32UniformRange.product_magnitude a a 305 (by decide) (by decide) ha ha h.squareRange
  have hw := F32UniformRange.product_magnitude (GeluArgumentError.square a) 0x3D372713 300
    (by decide) (by decide) hs.1 GeluArgumentError.coefficient_finite h.weightedRange
  have hf := F32AdditionBounds.add_real_error (GeluArgumentError.weighted a) 0x3F800000 152
    (by decide) hw.1 Gpt2RowInvStd.DenominatorError.one_finite h.factorRange
  rw [← F32Add.add_eq] at hf
  have hp := F32UniformRange.product_magnitude (GeluArgumentError.factor a) a 303
    (by decide) (by decide) hf.1 ha h.productRange
  constructor
  · apply (magnitude_bound _ _ hs.2).trans
    norm_num [F32UniformRange.productMagnitude]
  · apply (magnitude_bound _ _ hp.2).trans
    norm_num [F32UniformRange.productMagnitude]

theorem error_upper (a : UInt32) (ha : CodeLib.IEEE32.Finite a) (hx : |value a| ≤ 8)
    (h : GeluArgumentError.Ranges a bounds) : GeluArgumentError.error a bounds ≤ 1 / 30000 := by
  have hm := intermediates a ha h
  have hc : |Project.Gelu.Real.coefficient| ≤ 45 / 1000 := by
    norm_num [Project.Gelu.Real.coefficient]
  have hscale : |2 * Project.Gelu.Real.scale| ≤ 8 / 5 := by
    have hb := Project.Gelu.Real.scale_bounds
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * Project.Gelu.Real.scale)]
    linarith
  have hw : GeluArgumentError.weightedError a bounds ≤
      F32MultiplicationBounds.epsilon 300 + (129 / 100000000 + F32MultiplicationBounds.epsilon 305 * (45 / 1000)) := by
    unfold GeluArgumentError.weightedError
    dsimp only [bounds]
    apply add_le_add le_rfl
    apply add_le_add
    · simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right hm.1 (by norm_num : (0 : ℝ) ≤ 1 / 100000000)
    · exact mul_le_mul_of_nonneg_left hc (by unfold F32MultiplicationBounds.epsilon; positivity)
  have hp : GeluArgumentError.productError a bounds ≤
      F32MultiplicationBounds.epsilon 303 +
        (F32AdditionBounds.epsilon 152 + F32MultiplicationBounds.epsilon 300 +
          (129 / 100000000 + F32MultiplicationBounds.epsilon 305 * (45 / 1000))) * 8 := by
    unfold GeluArgumentError.productError
    dsimp only [bounds]
    apply add_le_add le_rfl
    dsimp only [bounds] at hw
    apply mul_le_mul (by linarith) hx (abs_nonneg _)
    norm_num [F32MultiplicationBounds.epsilon, F32AdditionBounds.epsilon]
  unfold GeluArgumentError.error
  dsimp only [bounds]
  have hp0 : 0 ≤ F32MultiplicationBounds.epsilon 303 +
      (F32AdditionBounds.epsilon 152 + F32MultiplicationBounds.epsilon 300 +
        (129 / 100000000 + F32MultiplicationBounds.epsilon 305 * (45 / 1000))) * 8 := by
    norm_num [F32MultiplicationBounds.epsilon, F32AdditionBounds.epsilon]
  have hprod := mul_le_mul hp hscale (abs_nonneg _) hp0
  dsimp only [bounds] at hprod
  have hsmall := mul_le_mul_of_nonneg_right hm.2 (by norm_num : (0 : ℝ) ≤ 1 / 10000000)
  norm_num [F32MultiplicationBounds.epsilon, F32AdditionBounds.epsilon] at hprod ⊢
  linarith

#print axioms error_upper
end Project.Gpt2CachedStep.GeluArgumentUniform
