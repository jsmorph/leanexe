import Interpreter.Wasm.IEEE32
import LeanExe.WGSL.ArtifactExecution

namespace Project.WGSL.Binary32

open LeanExe.WGSL

/-- Exact fused numerator in units of 2^-298. No intermediate product rounding
occurs. The shared Talos dyadic rounder performs one final nearest/even round. -/
def fusedNumerator (a b c : UInt32) : Int :=
  Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b +
    Wasm.IEEE32.scaledValue c * 2 ^ 149

/-- IEEE nearest/even fused multiply-add with preserved subnormals and zero
signs. Canonical NaNs make this total; finite-domain numerical theorems must
exclude exceptional intermediates before asserting a WGSL error bound. -/
def fma (a b c : UInt32) : UInt32 :=
  let negative := Wasm.IEEE32.sign a != Wasm.IEEE32.sign b
  if Wasm.IEEE32.isNaN a || Wasm.IEEE32.isNaN b || Wasm.IEEE32.isNaN c then
    Wasm.IEEE32.canonicalNaN
  else if Wasm.IEEE32.isInfinite a || Wasm.IEEE32.isInfinite b then
    if Wasm.IEEE32.scaledMagnitude a == 0 || Wasm.IEEE32.scaledMagnitude b == 0 then
      Wasm.IEEE32.canonicalNaN
    else if Wasm.IEEE32.isInfinite c && Wasm.IEEE32.sign c != negative then
      Wasm.IEEE32.canonicalNaN
    else Wasm.IEEE32.infinity negative
  else if Wasm.IEEE32.isInfinite c then c
  else
    let numerator := fusedNumerator a b c
    if numerator == 0 then Wasm.IEEE32.signMask (negative && Wasm.IEEE32.sign c)
    else Wasm.IEEE32.roundDyadicMagnitude (numerator < 0) numerator.natAbs 149

/-- Only the implemented scalar choice is inhabited. Unsupported choices do
not silently fall back to a different policy. -/
def semantics : ScalarSemantics where
  add choice x y z := choice = ieeeChoice ∧ z = Wasm.IEEE32.add x y
  mul choice x y z := choice = ieeeChoice ∧ z = Wasm.IEEE32.mul x y
  fma choice x y z result := choice = ieeeChoice ∧ result = fma x y z

def arithmetic : ScalarArithmetic := ⟨Wasm.IEEE32.add, Wasm.IEEE32.mul⟩

theorem total : ScalarTotal semantics ieeeChoice :=
  ⟨fun _ _ => ⟨_, rfl, rfl⟩, fun _ _ => ⟨_, rfl, rfl⟩, fun _ _ _ => ⟨_, rfl, rfl⟩⟩

theorem separate : SeparateInterpretation semantics arithmetic where
  add _ _ _ := by simp [semantics, arithmetic]
  mul _ _ _ := by simp [semantics, arithmetic]

def rectangularSeparate : DispatchArtifact RectangularArtifact.source semantics restricted :=
  RectangularArtifact.dispatchArtifact rfl rfl total

def rectangularFusion : DispatchArtifact RectangularArtifact.source semantics fusion :=
  RectangularArtifact.dispatchArtifact rfl True.intro total

theorem rectangular_exact (input : Dispatch.Input)
    (hb : input.buffers.Valid RectangularArtifact.ast.config) (output : WordBuffer)
    (run : (Dispatch.model semantics).Exec restricted RectangularArtifact.checked input output)
    {row col : Nat} (hr : row < 3) (hc : col < 5) :
    output (row * 5 + col) =
      gemmCell arithmetic RectangularArtifact.ast.config input.buffers.a input.buffers.b row col :=
  rectangularSeparate.exact separate input hb output run hr hc

#print axioms total
#print axioms rectangularSeparate
#print axioms rectangularFusion
#print axioms rectangular_exact

end Project.WGSL.Binary32
