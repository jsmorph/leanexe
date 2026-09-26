import Project.ProofKit.F32ErrorPropagation

namespace Project.ProofKit.F32HornerError
open CodeLib.IEEE32

def compute (input initial : UInt32) (coefficient : Nat → UInt32) (count : Nat) : UInt32 :=
  (List.range count).foldl (fun acc i => LeanExe.Float32.addBits
    (LeanExe.Float32.mulBits acc input) (coefficient i)) initial

noncomputable def reference (input initial : ℝ) (coefficient : Nat → ℝ) : Nat → ℝ
  | 0 => initial
  | count + 1 => reference input initial coefficient count * input + coefficient count

noncomputable def error (input initial : UInt32) (coefficient : Nat → UInt32)
    (referenceInput inputError initialError : ℝ) (coefficientError : Nat → ℝ)
    (mulBounds addBounds : Nat → Nat) : Nat → ℝ
  | 0 => initialError
  | count + 1 => F32AdditionBounds.epsilon (addBounds count) +
    (F32MultiplicationBounds.epsilon (mulBounds count) +
      (|value (compute input initial coefficient count)| * inputError +
        error input initial coefficient referenceInput inputError initialError coefficientError mulBounds addBounds count * |referenceInput|) +
      coefficientError count)

theorem compute_succ (input initial : UInt32) (coefficient : Nat → UInt32) (count : Nat) :
    compute input initial coefficient (count + 1) =
      LeanExe.Float32.addBits (LeanExe.Float32.mulBits (compute input initial coefficient count) input) (coefficient count) := by
  simp only [compute, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem horner_error (input initial : UInt32) (coefficient : Nat → UInt32)
    (X initialReference inputError initialError : ℝ) (C coefficientError : Nat → ℝ)
    (mulBounds addBounds : Nat → Nat) (count : Nat)
    (hInput : CodeLib.IEEE32.Finite input) (hInitial : CodeLib.IEEE32.Finite initial)
    (hInputError : |value input - X| ≤ inputError) (hInitialError : |value initial - initialReference| ≤ initialError)
    (hCoefficient : ∀ i < count, CodeLib.IEEE32.Finite (coefficient i))
    (hCoefficientError : ∀ i < count, |value (coefficient i) - C i| ≤ coefficientError i)
    (hMulLower : ∀ i < count, 173 ≤ mulBounds i) (hMulUpper : ∀ i < count, mulBounds i ≤ 425)
    (hMulRange : ∀ i < count,
      Wasm.IEEE32.scaledMagnitude (compute input initial coefficient i) * Wasm.IEEE32.scaledMagnitude input < 2 ^ mulBounds i)
    (hAddUpper : ∀ i < count, addBounds i ≤ 276)
    (hAddRange : ∀ i < count,
      (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (compute input initial coefficient i) input) +
        Wasm.IEEE32.scaledValue (coefficient i)).natAbs < 2 ^ addBounds i) :
    CodeLib.IEEE32.Finite (compute input initial coefficient count) ∧
      |value (compute input initial coefficient count) - reference X initialReference C count| ≤
        error input initial coefficient X inputError initialError coefficientError mulBounds addBounds count := by
  induction count with
  | zero => exact ⟨hInitial, hInitialError⟩
  | succ count ih =>
    have hPrevious := ih (fun i hi => hCoefficient i (by omega)) (fun i hi => hCoefficientError i (by omega))
      (fun i hi => hMulLower i (by omega)) (fun i hi => hMulUpper i (by omega))
      (fun i hi => hMulRange i (by omega)) (fun i hi => hAddUpper i (by omega)) (fun i hi => hAddRange i (by omega))
    have hMul := F32ErrorPropagation.mul (compute input initial coefficient count) input
      (reference X initialReference C count) X
      (error input initial coefficient X inputError initialError coefficientError mulBounds addBounds count) inputError
      (mulBounds count) hPrevious.1 hInput (hMulLower count (by omega)) (hMulUpper count (by omega))
      (hMulRange count (by omega)) hPrevious.2 hInputError
    have hAdd := F32ErrorPropagation.add (LeanExe.Float32.mulBits (compute input initial coefficient count) input)
      (coefficient count) (reference X initialReference C count * X) (C count)
      (F32MultiplicationBounds.epsilon (mulBounds count) +
        (|value (compute input initial coefficient count)| * inputError +
          error input initial coefficient X inputError initialError coefficientError mulBounds addBounds count * |X|))
      (coefficientError count) (addBounds count) hMul.1 (hCoefficient count (by omega))
      (hAddUpper count (by omega)) (hAddRange count (by omega)) hMul.2 (hCoefficientError count (by omega))
    simpa only [compute_succ, reference, error] using hAdd

#print axioms horner_error
end Project.ProofKit.F32HornerError
