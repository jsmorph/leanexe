import LeanExe.IEEE64
import Interpreter.Wasm.IEEE64

/-! Equalities for the arithmetic operations called by executable source.
Small helper equalities prevent definitional reduction from expanding large
integer powers while comparing the two namespaces. -/
namespace Project.SpectralKL.Operations
set_option linter.unusedSimpArgs false

theorem roundShift_eq : LeanExe.IEEE64.roundShift = Wasm.IEEE32.roundShift := by
  funext a b
  simp only [LeanExe.IEEE64.roundShift, Wasm.IEEE32.roundShift]

theorem roundQuotient_eq : LeanExe.IEEE64.roundQuotient = Wasm.IEEE32.roundQuotient := by
  funext a b
  simp only [LeanExe.IEEE64.roundQuotient, Wasm.IEEE32.roundQuotient, roundShift_eq]

theorem roundSqrtIntegral_eq : LeanExe.IEEE64.roundSqrtIntegral = Wasm.IEEE32.roundSqrtIntegral := by
  funext a b
  simp only [LeanExe.IEEE64.roundSqrtIntegral, Wasm.IEEE32.roundSqrtIntegral, roundShift_eq, roundQuotient_eq]

theorem canonicalNaN_eq : LeanExe.IEEE64.canonicalNaN = Wasm.IEEE64.canonicalNaN := by
  simp only [LeanExe.IEEE64.canonicalNaN, Wasm.IEEE64.canonicalNaN, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq]

theorem sign_eq : LeanExe.IEEE64.sign = Wasm.IEEE64.sign := by
  funext a
  simp only [LeanExe.IEEE64.sign, Wasm.IEEE64.sign, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq]

theorem exponent_eq : LeanExe.IEEE64.exponent = Wasm.IEEE64.exponent := by
  funext a
  simp only [LeanExe.IEEE64.exponent, Wasm.IEEE64.exponent, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq]

theorem fraction_eq : LeanExe.IEEE64.fraction = Wasm.IEEE64.fraction := by
  funext a
  simp only [LeanExe.IEEE64.fraction, Wasm.IEEE64.fraction, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq]

theorem isNaN_eq : LeanExe.IEEE64.isNaN = Wasm.IEEE64.isNaN := by
  funext a
  simp only [LeanExe.IEEE64.isNaN, Wasm.IEEE64.isNaN, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq]

theorem isInfinite_eq : LeanExe.IEEE64.isInfinite = Wasm.IEEE64.isInfinite := by
  funext a
  simp only [LeanExe.IEEE64.isInfinite, Wasm.IEEE64.isInfinite, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq]

theorem isFinite_eq : LeanExe.IEEE64.isFinite = Wasm.IEEE64.isFinite := by
  funext a
  simp only [LeanExe.IEEE64.isFinite, Wasm.IEEE64.isFinite, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq]

theorem scaledMagnitude_eq : LeanExe.IEEE64.scaledMagnitude = Wasm.IEEE64.scaledMagnitude := by
  funext a
  simp only [LeanExe.IEEE64.scaledMagnitude, Wasm.IEEE64.scaledMagnitude, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq]

theorem scaledValue_eq : LeanExe.IEEE64.scaledValue = Wasm.IEEE64.scaledValue := by
  funext a
  simp only [LeanExe.IEEE64.scaledValue, Wasm.IEEE64.scaledValue, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq]

theorem signMask_eq : LeanExe.IEEE64.signMask = Wasm.IEEE64.signMask := by
  funext a
  simp only [LeanExe.IEEE64.signMask, Wasm.IEEE64.signMask, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq]

theorem infinity_eq : LeanExe.IEEE64.infinity = Wasm.IEEE64.infinity := by
  funext a
  simp only [LeanExe.IEEE64.infinity, Wasm.IEEE64.infinity, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq]

theorem encodeFinite_eq : LeanExe.IEEE64.encodeFinite = Wasm.IEEE64.encodeFinite := by
  funext a b c
  simp only [LeanExe.IEEE64.encodeFinite, Wasm.IEEE64.encodeFinite, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq]

theorem negate_eq : LeanExe.IEEE64.negate = Wasm.IEEE64.negate := by
  funext a
  simp only [LeanExe.IEEE64.negate, Wasm.IEEE64.negate, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq]

theorem abs_eq : LeanExe.IEEE64.abs = Wasm.IEEE64.abs := by
  funext a
  simp only [LeanExe.IEEE64.abs, Wasm.IEEE64.abs, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq]

theorem copySign_eq : LeanExe.IEEE64.copySign = Wasm.IEEE64.copySign := by
  funext a b
  simp only [LeanExe.IEEE64.copySign, Wasm.IEEE64.copySign, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq]

theorem roundScaledMagnitude_eq : LeanExe.IEEE64.roundScaledMagnitude = Wasm.IEEE64.roundScaledMagnitude := by
  funext a b
  simp only [LeanExe.IEEE64.roundScaledMagnitude, Wasm.IEEE64.roundScaledMagnitude, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq]

theorem roundDyadicMagnitude_eq : LeanExe.IEEE64.roundDyadicMagnitude = Wasm.IEEE64.roundDyadicMagnitude := by
  funext a b c
  simp only [LeanExe.IEEE64.roundDyadicMagnitude, Wasm.IEEE64.roundDyadicMagnitude, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq]

theorem roundRationalMagnitude_eq : LeanExe.IEEE64.roundRationalMagnitude = Wasm.IEEE64.roundRationalMagnitude := by
  funext a b c
  simp only [LeanExe.IEEE64.roundRationalMagnitude, Wasm.IEEE64.roundRationalMagnitude, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq, roundDyadicMagnitude_eq]

theorem roundSqrtMagnitude_eq : LeanExe.IEEE64.roundSqrtMagnitude = Wasm.IEEE64.roundSqrtMagnitude := by
  funext a
  simp only [LeanExe.IEEE64.roundSqrtMagnitude, Wasm.IEEE64.roundSqrtMagnitude, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq, roundDyadicMagnitude_eq, roundRationalMagnitude_eq]

theorem add : LeanExe.IEEE64.addBits = Wasm.IEEE64.add := by
  funext a b
  simp only [LeanExe.IEEE64.addBits, Wasm.IEEE64.add, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq, roundDyadicMagnitude_eq, roundRationalMagnitude_eq, roundSqrtMagnitude_eq]

theorem sub : LeanExe.IEEE64.subBits = Wasm.IEEE64.sub := by
  funext a b
  simp only [LeanExe.IEEE64.subBits, Wasm.IEEE64.sub, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq, roundDyadicMagnitude_eq, roundRationalMagnitude_eq, roundSqrtMagnitude_eq, add]

theorem mul : LeanExe.IEEE64.mulBits = Wasm.IEEE64.mul := by
  funext a b
  simp only [LeanExe.IEEE64.mulBits, Wasm.IEEE64.mul, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq, roundDyadicMagnitude_eq, roundRationalMagnitude_eq, roundSqrtMagnitude_eq, add, sub]

theorem div : LeanExe.IEEE64.divBits = Wasm.IEEE64.div := by
  funext a b
  simp only [LeanExe.IEEE64.divBits, Wasm.IEEE64.div, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq, roundDyadicMagnitude_eq, roundRationalMagnitude_eq, roundSqrtMagnitude_eq, add, sub, mul]

theorem sqrt : LeanExe.IEEE64.sqrtBits = Wasm.IEEE64.sqrt := by
  funext a
  simp only [LeanExe.IEEE64.sqrtBits, Wasm.IEEE64.sqrt, roundShift_eq, roundQuotient_eq, roundSqrtIntegral_eq, canonicalNaN_eq, sign_eq, exponent_eq, fraction_eq, isNaN_eq, isInfinite_eq, isFinite_eq, scaledMagnitude_eq, scaledValue_eq, signMask_eq, infinity_eq, encodeFinite_eq, negate_eq, abs_eq, copySign_eq, roundScaledMagnitude_eq, roundDyadicMagnitude_eq, roundRationalMagnitude_eq, roundSqrtMagnitude_eq, add, sub, mul, div]

#print axioms add
#print axioms sub
#print axioms mul
#print axioms div
#print axioms sqrt
end Project.SpectralKL.Operations
