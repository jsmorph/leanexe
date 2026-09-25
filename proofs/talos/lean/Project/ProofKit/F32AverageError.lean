import Project.ProofKit.F32SumError
import Project.ProofKit.F32ErrorPropagation

set_option exponentiation.threshold 512

namespace Project.ProofKit.F32AverageError
open CodeLib.IEEE32

theorem divisor_finite : CodeLib.IEEE32.Finite 0x44400000 := by
  change Wasm.IEEE32.isFinite 0x44400000 = true
  decide

theorem divisor_value : value 0x44400000 = 768 := by
  norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
    Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]

def compute (input : Nat → UInt32) : UInt32 :=
  LeanExe.Float32.divBits (F32SumError.sumPrefix input 768) 0x44400000

noncomputable def error (inputError : Nat → ℝ) (addBounds : Nat → Nat) (divBound : Nat) : ℝ :=
  F32DivisionBounds.epsilon divBound +
    (∑ i ∈ Finset.range 768, (inputError i + F32AdditionBounds.epsilon (addBounds i))) / 768

theorem average_error (input : Nat → UInt32) (reference inputError : Nat → ℝ)
    (addBounds : Nat → Nat) (divBound : Nat)
    (hFinite : ∀ i < 768, CodeLib.IEEE32.Finite (input i))
    (hError : ∀ i < 768, |value (input i) - reference i| ≤ inputError i)
    (hAddUpper : ∀ i < 768, addBounds i ≤ 276)
    (hAddRange : ∀ i < 768,
      (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input i) + Wasm.IEEE32.scaledValue (input i)).natAbs < 2 ^ addBounds i)
    (hDivLower : 24 ≤ divBound) (hDivUpper : divBound ≤ 275)
    (hDivRange : Wasm.IEEE32.scaledMagnitude (F32SumError.sumPrefix input 768) * 2 ^ 149 ≤
      Wasm.IEEE32.scaledMagnitude 0x44400000 * 2 ^ divBound) :
    CodeLib.IEEE32.Finite (compute input) ∧
      |value (compute input) - (∑ i ∈ Finset.range 768, reference i) / 768| ≤ error inputError addBounds divBound := by
  have hSum := F32SumError.ordered_error input reference inputError addBounds 768 hFinite hError hAddUpper hAddRange
  have hDiv := F32ErrorPropagation.div (F32SumError.sumPrefix input 768) 0x44400000
    (∑ i ∈ Finset.range 768, reference i) 768
    (∑ i ∈ Finset.range 768, (inputError i + F32AdditionBounds.epsilon (addBounds i))) 0 768 divBound
    hSum.1 divisor_finite hDivLower hDivUpper (by decide) hDivRange (by norm_num)
    (by rw [divisor_value]; norm_num) (by norm_num) hSum.2 (by rw [divisor_value]; norm_num)
  simpa only [compute, error, mul_zero, add_zero] using hDiv

#print axioms average_error
end Project.ProofKit.F32AverageError
