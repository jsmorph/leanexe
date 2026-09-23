import Project.Gpt2CachedStep.ExpNeg.Perturbation
import Project.Gpt2RowInvStd.DenominatorError
import Project.Gelu.GlobalPerturbation
import Project.ProofKit.F32Absolute

set_option exponentiation.threshold 512

namespace Project.Gpt2CachedStep.GeluArgumentError
open Project.ProofKit CodeLib.IEEE32

def square (a : UInt32) : UInt32 := LeanExe.Float32.mulBits a a
def weighted (a : UInt32) : UInt32 := LeanExe.Float32.mulBits (square a) 0x3D372713
def factor (a : UInt32) : UInt32 := LeanExe.Float32.addBits (weighted a) 0x3F800000
def product (a : UInt32) : UInt32 := LeanExe.Float32.mulBits (factor a) a
def magnitude (a : UInt32) : UInt32 := LeanExe.Float32.mulBits (product a) 0x3FCC422A

theorem coefficient_finite : CodeLib.IEEE32.Finite 0x3D372713 := by
  change Wasm.IEEE32.isFinite 0x3D372713 = true
  decide

theorem scale_finite : CodeLib.IEEE32.Finite 0x3FCC422A := by
  change Wasm.IEEE32.isFinite 0x3FCC422A = true
  decide

theorem coefficient_error : |value 0x3D372713 - Project.Gelu.Real.coefficient| ≤ 1 / 100000000 := by
  norm_num [Project.Gelu.Real.coefficient, value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
    Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]

theorem scale_error : |value 0x3FCC422A - 2 * Project.Gelu.Real.scale| ≤ 1 / 10000000 := by
  have h := Project.Gelu.Real.scale_bounds_precise
  norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
    Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

structure Bounds where
  square : Nat
  weighted : Nat
  factor : Nat
  product : Nat
  magnitude : Nat

structure Ranges (a : UInt32) (b : Bounds) : Prop where
  squareLower : 173 ≤ b.square
  squareUpper : b.square ≤ 425
  squareRange : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude a < 2 ^ b.square
  weightedLower : 173 ≤ b.weighted
  weightedUpper : b.weighted ≤ 425
  weightedRange : Wasm.IEEE32.scaledMagnitude (square a) * Wasm.IEEE32.scaledMagnitude 0x3D372713 < 2 ^ b.weighted
  factorUpper : b.factor ≤ 276
  factorRange : (Wasm.IEEE32.scaledValue (weighted a) + Wasm.IEEE32.scaledValue 0x3F800000).natAbs < 2 ^ b.factor
  productLower : 173 ≤ b.product
  productUpper : b.product ≤ 425
  productRange : Wasm.IEEE32.scaledMagnitude (factor a) * Wasm.IEEE32.scaledMagnitude a < 2 ^ b.product
  magnitudeLower : 173 ≤ b.magnitude
  magnitudeUpper : b.magnitude ≤ 425
  magnitudeRange : Wasm.IEEE32.scaledMagnitude (product a) * Wasm.IEEE32.scaledMagnitude 0x3FCC422A < 2 ^ b.magnitude

noncomputable def weightedError (a : UInt32) (b : Bounds) : ℝ :=
  F32MultiplicationBounds.epsilon b.weighted +
    (|value (square a)| * (1 / 100000000) + F32MultiplicationBounds.epsilon b.square * |Project.Gelu.Real.coefficient|)

noncomputable def productError (a : UInt32) (b : Bounds) : ℝ :=
  F32MultiplicationBounds.epsilon b.product + (F32AdditionBounds.epsilon b.factor + weightedError a b) * |value a|

noncomputable def error (a : UInt32) (b : Bounds) : ℝ :=
  F32MultiplicationBounds.epsilon b.magnitude +
    (|value (product a)| * (1 / 10000000) + productError a b * |2 * Project.Gelu.Real.scale|)

theorem magnitude_error (a : UInt32) (b : Bounds) (ha : CodeLib.IEEE32.Finite a) (h : Ranges a b) :
    CodeLib.IEEE32.Finite (magnitude a) ∧
      |value (magnitude a) - Project.Gelu.Real.argument (value a)| ≤ error a b := by
  have hSquare := F32MultiplicationBounds.mul_real_error a a b.square h.squareLower h.squareUpper ha ha h.squareRange
  rw [← F32Mul.mul_eq] at hSquare
  have hWeighted := F32ErrorPropagation.mul (square a) 0x3D372713 (value a * value a) Project.Gelu.Real.coefficient
    (F32MultiplicationBounds.epsilon b.square) (1 / 100000000) b.weighted
    hSquare.1 coefficient_finite h.weightedLower h.weightedUpper h.weightedRange hSquare.2 coefficient_error
  have hFactor := F32ErrorPropagation.add (weighted a) 0x3F800000 (value a * value a * Project.Gelu.Real.coefficient) 1
    (weightedError a b) 0 b.factor hWeighted.1 Project.Gpt2RowInvStd.DenominatorError.one_finite h.factorUpper h.factorRange
    hWeighted.2 (by rw [Project.Gpt2RowInvStd.DenominatorError.one_value]; simp)
  simp only [add_zero] at hFactor
  have hProduct := F32ErrorPropagation.mul (factor a) a (value a * value a * Project.Gelu.Real.coefficient + 1) (value a)
    (F32AdditionBounds.epsilon b.factor + weightedError a b) 0 b.product
    hFactor.1 ha h.productLower h.productUpper h.productRange hFactor.2 (by simp)
  simp only [mul_zero, zero_add] at hProduct
  have hMagnitude := F32ErrorPropagation.mul (product a) 0x3FCC422A
    ((value a * value a * Project.Gelu.Real.coefficient + 1) * value a) (2 * Project.Gelu.Real.scale)
    (productError a b) (1 / 10000000) b.magnitude
    hProduct.1 scale_finite h.magnitudeLower h.magnitudeUpper h.magnitudeRange hProduct.2 scale_error
  have hReference : (value a * value a * Project.Gelu.Real.coefficient + 1) * value a * (2 * Project.Gelu.Real.scale) =
      Project.Gelu.Real.argument (value a) := by unfold Project.Gelu.Real.argument; ring
  rw [hReference] at hMagnitude
  exact hMagnitude

theorem negative_argument_error (a : UInt32) (b : Bounds) (ha : CodeLib.IEEE32.Finite a)
    (hPositive : 0 ≤ value a) (h : Ranges a b) :
    CodeLib.IEEE32.Finite (magnitude a ||| 0x80000000) ∧
      value (magnitude a ||| 0x80000000) ≤ 0 ∧
      |value (magnitude a ||| 0x80000000) - -Project.Gelu.Real.argument (value a)| ≤ error a b := by
  have hm := magnitude_error a b ha h
  rw [← F32Order.negativeAbsBits_eq_or]
  refine ⟨F32Order.negativeAbsBits_finite _ hm.1, ?_, ?_⟩
  · rw [F32Order.negativeAbsBits_value]
    exact neg_nonpos.mpr (abs_nonneg _)
  · rw [F32Order.negativeAbsBits_value, neg_sub_neg, abs_sub_comm]
    have hArg := Project.Gelu.Real.argument_nonnegative (value a) hPositive
    simpa only [abs_of_nonneg hArg] using (abs_abs_sub_abs_le _ _).trans hm.2

#print axioms magnitude_error
#print axioms negative_argument_error
end Project.Gpt2CachedStep.GeluArgumentError
