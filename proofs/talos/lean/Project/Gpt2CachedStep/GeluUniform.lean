import Project.Gpt2CachedStep.GeluArgumentUniform
import Project.Gpt2CachedStep.GeluRangeCertificate
import Project.Gpt2CachedStep.ExpNeg.UniformError

set_option exponentiation.threshold 512

namespace Project.Gpt2CachedStep.GeluUniform
open Project.ProofKit CodeLib.IEEE32

noncomputable def bounds : GeluForwardError.Bounds := GeluRangeCertificate.bounds {}

theorem inner_upper (a : UInt32) (ha : CodeLib.IEEE32.Finite a) (hn : 0 ≤ value a)
    (hx : |value a| ≤ 8) (h : GeluForwardError.Ranges a bounds) :
    GeluForwardError.positiveError a bounds ≤ 1 / 16 ∧
      GeluForwardError.negativeError a bounds ≤ 1 / 16 := by
  have harg := GeluArgumentError.negative_argument_error a GeluArgumentUniform.bounds ha hn h.argument
  have he := ExpNeg.UniformError.error_upper (GeluError.argument a) harg.2.1 h.expRanges
  have hg := GeluArgumentUniform.error_upper a ha hx h.argument
  have hexp : GeluForwardError.expError a bounds ≤ 101 / 30000 := by
    change ExpNeg.ForwardError.error (GeluError.argument a) (fun _ => 299) (fun _ => 151) (fun _ => 299) +
      GeluArgumentError.error a GeluArgumentUniform.bounds ≤ _
    linarith
  have hden : GeluForwardError.denError a bounds ≤ F32AdditionBounds.epsilon 151 + 101 / 30000 :=
    add_le_add le_rfl hexp
  have hpos : |value a / GeluError.referenceDenominator a| ≤ 8 := by
    have hm := (Project.Gelu.Real.gelu_magnitude (value a)).trans hx
    rw [Project.Gelu.Real.gelu_logistic] at hm
    exact hm
  have hneg : |-value a * GeluError.referenceExponential a / GeluError.referenceDenominator a| ≤ 8 := by
    unfold GeluError.referenceDenominator GeluError.referenceExponential
    rw [GeluError.negative_reference]
    exact (Project.Gelu.Real.gelu_magnitude (-value a)).trans (by simpa only [abs_neg] using hx)
  have hp := mul_le_mul hden hpos (abs_nonneg _) (by unfold F32AdditionBounds.epsilon; positivity)
  have hn' := mul_le_mul hden hneg (abs_nonneg _) (by unfold F32AdditionBounds.epsilon; positivity)
  have he' := mul_le_mul hexp hx (abs_nonneg _) (by norm_num)
  constructor
  · change F32DivisionBounds.epsilon 153 + |value a / GeluError.referenceDenominator a| *
      GeluForwardError.denError a bounds / 1 ≤ _
    norm_num [F32DivisionBounds.epsilon, F32AdditionBounds.epsilon] at hp ⊢
    nlinarith
  · change F32DivisionBounds.epsilon 153 +
      (F32MultiplicationBounds.epsilon 302 + |value a| * GeluForwardError.expError a bounds +
        |-value a * GeluError.referenceExponential a / GeluError.referenceDenominator a| *
          GeluForwardError.denError a bounds) / 1 ≤ _
    norm_num [F32DivisionBounds.epsilon, F32MultiplicationBounds.epsilon, F32AdditionBounds.epsilon] at hn' ⊢
    nlinarith

theorem error_upper (input : UInt32) (ha : CodeLib.IEEE32.Finite input)
    (h : ¬F32Order.absBits input > 0x41000000 → GeluForwardError.Ranges (F32Order.absBits input) bounds) :
    GeluForwardError.error input bounds ≤ 1 / 16 := by
  unfold GeluForwardError.error
  split_ifs with hcut hsign
  · norm_num
  all_goals
    have horder : F32Order.absBits input ≤ F32Order.absBits 0x41000000 := by
      change (F32Order.absBits input).toNat ≤ (F32Order.absBits 0x41000000).toNat
      change ¬(0x41000000 : UInt32).toNat < (F32Order.absBits input).toNat at hcut
      exact Nat.le_of_not_gt hcut
    have hx := F32Order.abs_value_mono input 0x41000000 horder
    have height : value (0x41000000 : UInt32) = 8 := by
      norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
    rw [height, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at hx
    have hi := inner_upper (F32Order.absBits input) (F32Order.absBits_finite input ha)
      (by rw [F32Order.absBits_value]; exact abs_nonneg _)
      (by simpa only [F32Order.absBits_value, abs_abs] using hx) (h hcut)
  · exact hi.1
  · exact hi.2

#print axioms error_upper
end Project.Gpt2CachedStep.GeluUniform
