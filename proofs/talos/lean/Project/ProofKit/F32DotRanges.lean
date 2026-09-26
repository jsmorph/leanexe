import Project.ProofKit.F32DotError

namespace Project.ProofKit.F32DotError
open CodeLib.IEEE32

structure Bounds where
  mulBound : Nat → Nat
  addBound : Nat → Nat

structure Ranges (x w : Nat → UInt32) (count : Nat) (b : Bounds) : Prop where
  inputFinite : ∀ i < count, CodeLib.IEEE32.Finite (x i)
  weightFinite : ∀ i < count, CodeLib.IEEE32.Finite (w i)
  mulLower : ∀ i < count, 173 ≤ b.mulBound i
  mulUpper : ∀ i < count, b.mulBound i ≤ 425
  mulRange : ∀ i < count, Wasm.IEEE32.scaledMagnitude (x i) * Wasm.IEEE32.scaledMagnitude (w i) < 2 ^ b.mulBound i
  addUpper : ∀ i < count, b.addBound i ≤ 276
  addRange : ∀ i < count, (Wasm.IEEE32.scaledValue (compute x w i) +
    Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (x i) (w i))).natAbs < 2 ^ b.addBound i

noncomputable def errorBound (x : Nat → UInt32) (W ex ew : Nat → ℝ) (count : Nat) (b : Bounds) : ℝ :=
  ∑ i ∈ Finset.range count, (F32MultiplicationBounds.epsilon (b.mulBound i) +
    (|value (x i)| * ew i + ex i * |W i|) + F32AdditionBounds.epsilon (b.addBound i))

theorem error_of_ranges (x w : Nat → UInt32) (X W ex ew : Nat → ℝ) (count : Nat) (b : Bounds)
    (h : Ranges x w count b) (hx : ∀ i < count, |value (x i) - X i| ≤ ex i)
    (hw : ∀ i < count, |value (w i) - W i| ≤ ew i) :
    CodeLib.IEEE32.Finite (compute x w count) ∧
      |value (compute x w count) - ∑ i ∈ Finset.range count, X i * W i| ≤ errorBound x W ex ew count b :=
  error x w X W ex ew b.mulBound b.addBound count h.inputFinite h.weightFinite hx hw
    h.mulLower h.mulUpper h.mulRange h.addUpper h.addRange

#print axioms error_of_ranges
end Project.ProofKit.F32DotError
