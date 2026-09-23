import Project.ProofKit.F32ErrorPropagation
import Project.ProofKit.F32SumError

namespace Project.ProofKit.F32DotError
open CodeLib.IEEE32

def compute (x w : Nat → UInt32) (count : Nat) : UInt32 :=
  F32SumError.sumPrefix (fun i => LeanExe.Float32.mulBits (x i) (w i)) count

theorem error (x w : Nat → UInt32) (X W ex ew : Nat → ℝ) (mulBounds addBounds : Nat → Nat)
    (count : Nat) (hx : ∀ i < count, CodeLib.IEEE32.Finite (x i))
    (hw : ∀ i < count, CodeLib.IEEE32.Finite (w i))
    (hex : ∀ i < count, |value (x i) - X i| ≤ ex i)
    (hew : ∀ i < count, |value (w i) - W i| ≤ ew i)
    (hMulLower : ∀ i < count, 173 ≤ mulBounds i) (hMulUpper : ∀ i < count, mulBounds i ≤ 425)
    (hMulRange : ∀ i < count,
      Wasm.IEEE32.scaledMagnitude (x i) * Wasm.IEEE32.scaledMagnitude (w i) < 2 ^ mulBounds i)
    (hAddUpper : ∀ i < count, addBounds i ≤ 276)
    (hAddRange : ∀ i < count, (Wasm.IEEE32.scaledValue (compute x w i) +
      Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (x i) (w i))).natAbs < 2 ^ addBounds i) :
    CodeLib.IEEE32.Finite (compute x w count) ∧
      |value (compute x w count) - ∑ i ∈ Finset.range count, X i * W i| ≤
        ∑ i ∈ Finset.range count, (F32MultiplicationBounds.epsilon (mulBounds i) +
          (|value (x i)| * ew i + ex i * |W i|) + F32AdditionBounds.epsilon (addBounds i)) := by
  have hProduct (i : Nat) (hi : i < count) :=
    F32ErrorPropagation.mul (x i) (w i) (X i) (W i) (ex i) (ew i) (mulBounds i)
      (hx i hi) (hw i hi) (hMulLower i hi) (hMulUpper i hi) (hMulRange i hi) (hex i hi) (hew i hi)
  exact F32SumError.ordered_error _ _ _ addBounds count
    (fun i hi => (hProduct i hi).1) (fun i hi => (hProduct i hi).2) hAddUpper hAddRange

#print axioms error
end Project.ProofKit.F32DotError
