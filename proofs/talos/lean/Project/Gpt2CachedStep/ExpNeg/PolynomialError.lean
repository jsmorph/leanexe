import Project.Gpt2CachedStep.ExpNeg.Source
import Project.ExpNeg.Real
import Project.ProofKit.F32HornerError

set_option exponentiation.threshold 512

namespace Project.Gpt2CachedStep.ExpNeg.PolynomialError
open Project.ProofKit CodeLib.IEEE32 LeanExe.Models.Gpt2

def coefficient (i : Nat) : UInt32 :=
  [0x274A963C, 0x29573F9F, 0x2B573F9F, 0x2D49CBA5, 0x2F309231, 0x310F76C7,
   0x32D7322B, 0x3493F27E, 0x3638EF1D, 0x37D00D01, 0x39500D01, 0x3AB60B61,
   0x3C088889, 0x3D2AAAAB, 0x3E2AAAAB, 0x3F000000, 0x3F800000, 0x3F800000][i]!

noncomputable def referenceCoefficient (i : Nat) : ℝ := 1 / ((17 - i).factorial : ℝ)
noncomputable def coefficientError : ℝ := 1 / 2 ^ 24

theorem source (input : UInt32) :
    expPolynomial input = F32HornerError.compute input 0x253413C3 coefficient 18 := rfl

theorem reference_polynomial (x : ℝ) :
    F32HornerError.reference x (1 / 6402373705728000) referenceCoefficient 18 = Project.ExpNeg.polynomialReal x := by
  norm_num [F32HornerError.reference, referenceCoefficient, Nat.factorial, Project.ExpNeg.polynomialReal]

theorem initial_finite : CodeLib.IEEE32.Finite 0x253413C3 := by
  change Wasm.IEEE32.isFinite 0x253413C3 = true
  decide

theorem initial_error : |value 0x253413C3 - (1 / 6402373705728000)| ≤ coefficientError := by
  norm_num [coefficientError, value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
    Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]

theorem coefficient_finite (i : Nat) (hi : i < 18) : CodeLib.IEEE32.Finite (coefficient i) := by
  interval_cases i <;> change Wasm.IEEE32.isFinite _ = true <;> decide

theorem coefficient_error (i : Nat) (hi : i < 18) : |value (coefficient i) - referenceCoefficient i| ≤ coefficientError := by
  interval_cases i <;>
    norm_num [coefficient, referenceCoefficient, Nat.factorial, coefficientError,
      value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
      Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]

noncomputable def error (input : UInt32) (mulBounds addBounds : Nat → Nat) : ℝ :=
  F32HornerError.error input 0x253413C3 coefficient (value input) 0 coefficientError
    (fun _ => coefficientError) mulBounds addBounds 18 + 1 / 100000000000000000

theorem polynomial_error (input : UInt32) (mulBounds addBounds : Nat → Nat)
    (hInput : CodeLib.IEEE32.Finite input) (hUnit : |value input| ≤ 1)
    (hMulLower : ∀ i < 18, 173 ≤ mulBounds i) (hMulUpper : ∀ i < 18, mulBounds i ≤ 425)
    (hMulRange : ∀ i < 18,
      Wasm.IEEE32.scaledMagnitude (F32HornerError.compute input 0x253413C3 coefficient i) *
        Wasm.IEEE32.scaledMagnitude input < 2 ^ mulBounds i)
    (hAddUpper : ∀ i < 18, addBounds i ≤ 276)
    (hAddRange : ∀ i < 18,
      (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (F32HornerError.compute input 0x253413C3 coefficient i) input) +
        Wasm.IEEE32.scaledValue (coefficient i)).natAbs < 2 ^ addBounds i) :
    CodeLib.IEEE32.Finite (expPolynomial input) ∧
      |value (expPolynomial input) - Real.exp (value input)| ≤ error input mulBounds addBounds := by
  have h := F32HornerError.horner_error input 0x253413C3 coefficient (value input) (1 / 6402373705728000)
    0 coefficientError referenceCoefficient (fun _ => coefficientError) mulBounds addBounds 18
    hInput initial_finite (by simp) initial_error coefficient_finite coefficient_error
    hMulLower hMulUpper hMulRange hAddUpper hAddRange
  rw [reference_polynomial, ← source] at h
  have hPolynomial := Project.ExpNeg.polynomialReal_error (value input) hUnit
  exact ⟨h.1, (abs_sub_le _ _ _).trans (add_le_add h.2 hPolynomial)⟩

#print axioms reference_polynomial
#print axioms coefficient_error
#print axioms polynomial_error
end Project.Gpt2CachedStep.ExpNeg.PolynomialError
