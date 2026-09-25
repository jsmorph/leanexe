import Project.Gpt2CachedStep.GeluError

set_option exponentiation.threshold 512

namespace Project.Gpt2CachedStep.GeluForwardError
open Project.ProofKit CodeLib.IEEE32 LeanExe.Models.Gpt2

structure Bounds where
  argument : GeluArgumentError.Bounds
  expMul : Nat → Nat
  expAdd : Nat → Nat
  expSquare : Nat → Nat
  denominatorAdd : Nat
  numeratorMul : Nat
  positiveDiv : Nat
  negativeDiv : Nat
  denominatorLower : ℝ

structure Ranges (a : UInt32) (b : Bounds) : Prop where
  argument : GeluArgumentError.Ranges a b.argument
  expCutoff : GeluError.argument a > 0xC2800000 → value (GeluError.argument a) ≤ -64
  expRanges : GeluError.argument a ≤ 0xC2800000 →
    ExpNeg.ForwardError.Ranges (GeluError.argument a) b.expMul b.expAdd b.expSquare
  denominatorUpper : b.denominatorAdd ≤ 276
  denominatorRange : (Wasm.IEEE32.scaledValue 0x3F800000 + Wasm.IEEE32.scaledValue (GeluError.exponential a)).natAbs < 2 ^ b.denominatorAdd
  lowerPositive : 0 < b.denominatorLower
  denominatorLower : b.denominatorLower ≤ |value (GeluError.denominator a)|
  denominatorNonzero : Wasm.IEEE32.scaledMagnitude (GeluError.denominator a) ≠ 0
  numeratorLower : 173 ≤ b.numeratorMul
  numeratorUpper : b.numeratorMul ≤ 425
  numeratorRange : Wasm.IEEE32.scaledMagnitude (a ||| 0x80000000) * Wasm.IEEE32.scaledMagnitude (GeluError.exponential a) < 2 ^ b.numeratorMul
  positiveLower : 24 ≤ b.positiveDiv
  positiveUpper : b.positiveDiv ≤ 275
  positiveRange : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ Wasm.IEEE32.scaledMagnitude (GeluError.denominator a) * 2 ^ b.positiveDiv
  negativeLower : 24 ≤ b.negativeDiv
  negativeUpper : b.negativeDiv ≤ 275
  negativeRange : Wasm.IEEE32.scaledMagnitude (GeluError.numerator a) * 2 ^ 149 ≤
    Wasm.IEEE32.scaledMagnitude (GeluError.denominator a) * 2 ^ b.negativeDiv

noncomputable def expError (a : UInt32) (b : Bounds) : ℝ :=
  ExpNeg.ForwardError.error (GeluError.argument a) b.expMul b.expAdd b.expSquare + GeluArgumentError.error a b.argument

noncomputable def denError (a : UInt32) (b : Bounds) : ℝ :=
  F32AdditionBounds.epsilon b.denominatorAdd + expError a b

noncomputable def positiveError (a : UInt32) (b : Bounds) : ℝ :=
  F32DivisionBounds.epsilon b.positiveDiv + |value a / GeluError.referenceDenominator a| * denError a b / b.denominatorLower

noncomputable def negativeError (a : UInt32) (b : Bounds) : ℝ :=
  F32DivisionBounds.epsilon b.negativeDiv +
    (GeluError.numeratorError a (expError a b) b.numeratorMul +
      |-value a * GeluError.referenceExponential a / GeluError.referenceDenominator a| * denError a b) / b.denominatorLower

theorem inner_error (a : UInt32) (b : Bounds) (ha : CodeLib.IEEE32.Finite a)
    (hNonnegative : 0 ≤ value a) (h : Ranges a b) :
    (CodeLib.IEEE32.Finite (GeluError.positivePart a) ∧
      |value (GeluError.positivePart a) - Project.Gelu.Real.gelu (value a)| ≤ positiveError a b) ∧
    (CodeLib.IEEE32.Finite (GeluError.negativePart a) ∧
      |value (GeluError.negativePart a) - Project.Gelu.Real.gelu (-value a)| ≤ negativeError a b) := by
  have hExp := GeluError.exponential_error a b.argument b.expMul b.expAdd b.expSquare ha hNonnegative h.argument h.expCutoff h.expRanges
  have hDen := GeluError.denominator_error a (expError a b) b.denominatorAdd hExp.1 hExp.2 h.denominatorUpper h.denominatorRange
  have hNum := GeluError.numerator_error a (expError a b) b.numeratorMul ha hNonnegative hExp.1 hExp.2
    h.numeratorLower h.numeratorUpper h.numeratorRange
  exact ⟨GeluError.positive_error a (denError a b) b.denominatorLower b.positiveDiv
      ha hDen.1 hDen.2 h.positiveLower h.positiveUpper h.denominatorNonzero h.positiveRange h.lowerPositive h.denominatorLower,
    GeluError.negative_error a (GeluError.numeratorError a (expError a b) b.numeratorMul) (denError a b)
      b.denominatorLower b.negativeDiv hNum.1 hDen.1 hNum.2 hDen.2 h.negativeLower h.negativeUpper h.denominatorNonzero
      h.negativeRange h.lowerPositive h.denominatorLower⟩

theorem cutoff_magnitude (input : UInt32) (h : F32Order.absBits input > 0x41000000) : 8 ≤ |value input| := by
  have hOrder : F32Order.absBits 0x41000000 ≤ F32Order.absBits input := by
    apply UInt32.le_iff_toNat_le.mpr
    exact (UInt32.lt_iff_toNat_lt.mp h).le
  have hValue := F32Order.abs_value_mono 0x41000000 input hOrder
  have hEight : value 0x41000000 = 8 := by
    norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
      Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
  simpa only [hEight, abs_of_pos (by norm_num : (0 : ℝ) < 8)] using hValue

noncomputable def error (input : UInt32) (b : Bounds) : ℝ :=
  if F32Order.absBits input > 0x41000000 then 1 / 100
  else if input < 0x80000000 then positiveError (F32Order.absBits input) b
  else negativeError (F32Order.absBits input) b

theorem source_error (input : UInt32) (b : Bounds) (hFinite : CodeLib.IEEE32.Finite input)
    (hRanges : ¬F32Order.absBits input > 0x41000000 → Ranges (F32Order.absBits input) b) :
    CodeLib.IEEE32.Finite (gelu input) ∧
      |value (gelu input) - Project.Gelu.Real.gelu (value input)| ≤ error input b := by
  rw [GeluError.source]
  by_cases hTail : F32Order.absBits input > 0x41000000
  · rw [ite_eq_left hTail]
    have hMagnitude := cutoff_magnitude input hTail
    by_cases hSign : input < 0x80000000
    · rw [ite_eq_left hSign]
      have hPositive := F32Order.value_nonnegative input hSign
      rw [abs_of_nonneg hPositive] at hMagnitude
      refine ⟨hFinite, ?_⟩
      simpa only [error, hTail, ite_true, abs_sub_comm] using Project.Gelu.Real.positive_tail (value input) (by linarith)
    · rw [ite_eq_right hSign]
      have hNegative := F32Order.value_nonpositive input hSign
      rw [abs_of_nonpos hNegative] at hMagnitude
      have hZero : value (0 : UInt32) = 0 := by
        norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
          Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
      refine ⟨by change Wasm.IEEE32.isFinite 0 = true; decide, ?_⟩
      simpa only [error, hTail, ite_true, hZero, zero_sub, abs_neg] using Project.Gelu.Real.negative_tail (value input) (by linarith)
  · rw [ite_eq_right hTail]
    have hInner := inner_error (F32Order.absBits input) b (F32Order.absBits_finite input hFinite)
      (by rw [F32Order.absBits_value]; exact abs_nonneg _) (hRanges hTail)
    by_cases hSign : input < 0x80000000
    · rw [ite_eq_left hSign]
      have hPositive := F32Order.value_nonnegative input hSign
      simpa only [error, hTail, hSign, ite_false, ite_true, F32Order.absBits_value, abs_of_nonneg hPositive] using hInner.1
    · rw [ite_eq_right hSign]
      have hNegative := F32Order.value_nonpositive input hSign
      simpa only [error, hTail, hSign, ite_false, F32Order.absBits_value, abs_of_nonpos hNegative, neg_neg] using hInner.2

theorem reference_error (input : UInt32) (reference inputError : ℝ) (b : Bounds)
    (hFinite : CodeLib.IEEE32.Finite input)
    (hRanges : ¬F32Order.absBits input > 0x41000000 → Ranges (F32Order.absBits input) b)
    (hInputError : |value input - reference| ≤ inputError) :
    CodeLib.IEEE32.Finite (gelu input) ∧
      |value (gelu input) - Project.Gelu.Real.gelu reference| ≤ error input b + 4 * inputError := by
  have h := source_error input b hFinite hRanges
  have hPerturbation := (Project.Gelu.Real.gelu_lipschitz_global (value input) reference).trans
    (mul_le_mul_of_nonneg_left hInputError (by norm_num))
  exact ⟨h.1, (abs_sub_le _ _ _).trans (add_le_add h.2 hPerturbation)⟩

#print axioms inner_error
#print axioms source_error
#print axioms reference_error
end Project.Gpt2CachedStep.GeluForwardError
