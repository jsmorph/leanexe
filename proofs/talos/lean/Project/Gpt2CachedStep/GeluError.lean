import Project.Gpt2CachedStep.GeluArgumentError

namespace Project.Gpt2CachedStep.GeluError
open Project.ProofKit CodeLib.IEEE32 LeanExe.Models.Gpt2

noncomputable def referenceExponential (a : UInt32) : ℝ := Real.exp (-Project.Gelu.Real.argument (value a))
noncomputable def referenceDenominator (a : UInt32) : ℝ := 1 + referenceExponential a

theorem exponential_error (a : UInt32) (argumentBounds : GeluArgumentError.Bounds)
    (mulBounds addBounds squareBounds : Nat → Nat)
    (ha : CodeLib.IEEE32.Finite a) (hPositive : 0 ≤ value a)
    (hArgument : GeluArgumentError.Ranges a argumentBounds)
    (hCutoff : argument a > 0xC2800000 → value (argument a) ≤ -64)
    (hRanges : argument a ≤ 0xC2800000 → ExpNeg.ForwardError.Ranges (argument a) mulBounds addBounds squareBounds) :
    CodeLib.IEEE32.Finite (exponential a) ∧
      |value (exponential a) - referenceExponential a| ≤
        ExpNeg.ForwardError.error (argument a) mulBounds addBounds squareBounds + GeluArgumentError.error a argumentBounds := by
  have hArg := GeluArgumentError.negative_argument_error a argumentBounds ha hPositive hArgument
  exact ExpNeg.Perturbation.exp_error (argument a) (-Project.Gelu.Real.argument (value a)) (GeluArgumentError.error a argumentBounds)
    mulBounds addBounds squareBounds hCutoff hRanges hArg.2.1
    (neg_nonpos.mpr (Project.Gelu.Real.argument_nonnegative (value a) hPositive)) hArg.2.2

theorem denominator_error (a : UInt32) (expError : ℝ) (bound : Nat)
    (hFinite : CodeLib.IEEE32.Finite (exponential a))
    (hError : |value (exponential a) - referenceExponential a| ≤ expError)
    (hUpper : bound ≤ 276)
    (hRange : (Wasm.IEEE32.scaledValue 0x3F800000 + Wasm.IEEE32.scaledValue (exponential a)).natAbs < 2 ^ bound) :
    CodeLib.IEEE32.Finite (denominator a) ∧
      |value (denominator a) - referenceDenominator a| ≤ F32AdditionBounds.epsilon bound + expError := by
  have h := F32ErrorPropagation.add 0x3F800000 (exponential a) 1 (referenceExponential a) 0 expError bound
    Project.Gpt2RowInvStd.DenominatorError.one_finite hFinite hUpper hRange
    (by rw [Project.Gpt2RowInvStd.DenominatorError.one_value]; simp) hError
  simpa only [denominator, referenceDenominator, zero_add] using h

theorem positive_error (a : UInt32) (denError lower : ℝ) (bound : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hDen : CodeLib.IEEE32.Finite (denominator a))
    (hDenError : |value (denominator a) - referenceDenominator a| ≤ denError)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 275)
    (hNonzero : Wasm.IEEE32.scaledMagnitude (denominator a) ≠ 0)
    (hRange : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ Wasm.IEEE32.scaledMagnitude (denominator a) * 2 ^ bound)
    (hl : 0 < lower) (hDenLower : lower ≤ |value (denominator a)|) :
    CodeLib.IEEE32.Finite (positivePart a) ∧
      |value (positivePart a) - Project.Gelu.Real.gelu (value a)| ≤
        F32DivisionBounds.epsilon bound + |value a / referenceDenominator a| * denError / lower := by
  have hReference : referenceDenominator a ≠ 0 := by unfold referenceDenominator referenceExponential; positivity
  have h := F32ErrorPropagation.div a (denominator a) (value a) (referenceDenominator a) 0 denError lower bound
    ha hDen hLower hUpper hNonzero hRange hl hDenLower hReference (by simp) hDenError
  rw [Project.Gelu.Real.gelu_logistic]
  simpa only [positivePart, referenceDenominator, referenceExponential, zero_add] using h

theorem negative_reference (a : ℝ) :
    (-a * Real.exp (-Project.Gelu.Real.argument a)) / (1 + Real.exp (-Project.Gelu.Real.argument a)) =
      Project.Gelu.Real.gelu (-a) := by
  rw [Project.Gelu.Real.gelu_neg, Project.Gelu.Real.gelu_logistic]
  have hNonzero : 1 + Real.exp (-Project.Gelu.Real.argument a) ≠ 0 := by positivity
  field_simp [hNonzero]
  ring

noncomputable def numeratorError (a : UInt32) (expError : ℝ) (mulBound : Nat) : ℝ :=
  F32MultiplicationBounds.epsilon mulBound + |value a| * expError

theorem numerator_error (a : UInt32) (expError : ℝ) (bound : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hPositive : 0 ≤ value a)
    (hExp : CodeLib.IEEE32.Finite (exponential a))
    (hExpError : |value (exponential a) - referenceExponential a| ≤ expError)
    (hLower : 173 ≤ bound) (hUpper : bound ≤ 425)
    (hRange : Wasm.IEEE32.scaledMagnitude (a ||| 0x80000000) * Wasm.IEEE32.scaledMagnitude (exponential a) < 2 ^ bound) :
    CodeLib.IEEE32.Finite (numerator a) ∧
      |value (numerator a) - -value a * referenceExponential a| ≤ numeratorError a expError bound := by
  have hNegative : value (a ||| 0x80000000) = -value a := by
    rw [← F32Order.negativeAbsBits_eq_or, F32Order.negativeAbsBits_value, abs_of_nonneg hPositive]
  have hNegativeFinite : CodeLib.IEEE32.Finite (a ||| 0x80000000) := by
    rw [← F32Order.negativeAbsBits_eq_or]
    exact F32Order.negativeAbsBits_finite a ha
  have h := F32ErrorPropagation.mul (a ||| 0x80000000) (exponential a) (-value a) (referenceExponential a)
    0 expError bound hNegativeFinite hExp hLower hUpper hRange (by rw [hNegative]; simp) hExpError
  simpa only [numerator, numeratorError, hNegative, abs_neg, zero_mul, add_zero] using h

theorem negative_error (a : UInt32) (numError denError lower : ℝ) (bound : Nat)
    (hNum : CodeLib.IEEE32.Finite (numerator a)) (hDen : CodeLib.IEEE32.Finite (denominator a))
    (hNumError : |value (numerator a) - -value a * referenceExponential a| ≤ numError)
    (hDenError : |value (denominator a) - referenceDenominator a| ≤ denError)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 275)
    (hNonzero : Wasm.IEEE32.scaledMagnitude (denominator a) ≠ 0)
    (hRange : Wasm.IEEE32.scaledMagnitude (numerator a) * 2 ^ 149 ≤ Wasm.IEEE32.scaledMagnitude (denominator a) * 2 ^ bound)
    (hl : 0 < lower) (hDenLower : lower ≤ |value (denominator a)|) :
    CodeLib.IEEE32.Finite (negativePart a) ∧
      |value (negativePart a) - Project.Gelu.Real.gelu (-value a)| ≤
        F32DivisionBounds.epsilon bound +
          (numError + |-value a * referenceExponential a / referenceDenominator a| * denError) / lower := by
  have hReference : referenceDenominator a ≠ 0 := by unfold referenceDenominator referenceExponential; positivity
  have h := F32ErrorPropagation.div (numerator a) (denominator a) (-value a * referenceExponential a)
    (referenceDenominator a) numError denError lower bound hNum hDen hLower hUpper hNonzero hRange
    hl hDenLower hReference hNumError hDenError
  have hReferenceEq : -value a * referenceExponential a / referenceDenominator a = Project.Gelu.Real.gelu (-value a) :=
    negative_reference (value a)
  rw [hReferenceEq] at h
  rw [hReferenceEq]
  exact h

theorem source (input : UInt32) : gelu input =
    if F32Order.absBits input > 0x41000000 then
      if input < 0x80000000 then input else 0
    else if input < 0x80000000 then positivePart (F32Order.absBits input)
      else negativePart (F32Order.absBits input) := rfl

#print axioms exponential_error
#print axioms denominator_error
#print axioms positive_error
#print axioms numerator_error
#print axioms negative_error
#print axioms source
end Project.Gpt2CachedStep.GeluError
