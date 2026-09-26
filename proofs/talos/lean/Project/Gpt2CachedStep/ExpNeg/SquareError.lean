import Project.Gpt2CachedStep.ExpNeg.PolynomialError

namespace Project.Gpt2CachedStep.ExpNeg.SquareError
open Project.ProofKit CodeLib.IEEE32

noncomputable def error (input : UInt32) (reference initialError : ℝ) (bounds : Nat → Nat) : Nat → ℝ
  | 0 => initialError
  | count + 1 => F32MultiplicationBounds.epsilon (bounds count) +
    (|value (squarePrefix input count)| * error input reference initialError bounds count +
      error input reference initialError bounds count * |reference ^ (2 ^ count)|)

theorem square_error (input : UInt32) (reference initialError : ℝ) (bounds : Nat → Nat) (count : Nat)
    (hFinite : CodeLib.IEEE32.Finite input) (hError : |value input - reference| ≤ initialError)
    (hLower : ∀ i < count, 173 ≤ bounds i) (hUpper : ∀ i < count, bounds i ≤ 425)
    (hRange : ∀ i < count,
      Wasm.IEEE32.scaledMagnitude (squarePrefix input i) * Wasm.IEEE32.scaledMagnitude (squarePrefix input i) < 2 ^ bounds i) :
    CodeLib.IEEE32.Finite (squarePrefix input count) ∧
      |value (squarePrefix input count) - reference ^ (2 ^ count)| ≤ error input reference initialError bounds count := by
  induction count with
  | zero => simpa only [squarePrefix_zero, pow_zero, pow_one, error] using And.intro hFinite hError
  | succ count ih =>
    have hPrevious := ih (fun i hi => hLower i (by omega)) (fun i hi => hUpper i (by omega)) (fun i hi => hRange i (by omega))
    have hMul := F32ErrorPropagation.mul (squarePrefix input count) (squarePrefix input count)
      (reference ^ (2 ^ count)) (reference ^ (2 ^ count))
      (error input reference initialError bounds count) (error input reference initialError bounds count) (bounds count)
      hPrevious.1 hPrevious.1 (hLower count (by omega)) (hUpper count (by omega)) (hRange count (by omega)) hPrevious.2 hPrevious.2
    rw [squarePrefix_succ, ← F32Mul.mul_eq]
    simpa only [error, pow_succ 2, pow_mul, pow_two] using hMul

theorem exp_reconstruction (input : UInt32) (x initialError : ℝ) (bounds : Nat → Nat) (count : Nat)
    (hFinite : CodeLib.IEEE32.Finite input) (hError : |value input - Real.exp x| ≤ initialError)
    (hLower : ∀ i < count, 173 ≤ bounds i) (hUpper : ∀ i < count, bounds i ≤ 425)
    (hRange : ∀ i < count,
      Wasm.IEEE32.scaledMagnitude (squarePrefix input i) * Wasm.IEEE32.scaledMagnitude (squarePrefix input i) < 2 ^ bounds i) :
    CodeLib.IEEE32.Finite (squarePrefix input count) ∧
      |value (squarePrefix input count) - Real.exp ((2 ^ count : Nat) * x)| ≤ error input (Real.exp x) initialError bounds count := by
  rw [Real.exp_nat_mul]
  exact square_error input (Real.exp x) initialError bounds count hFinite hError hLower hUpper hRange

#print axioms square_error
#print axioms exp_reconstruction
end Project.Gpt2CachedStep.ExpNeg.SquareError
