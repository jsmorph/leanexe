import Verified.Correct
import LeanExe.Encoding.RoundTrip

/-! The first program of the verified compiler: `a * b + c * c - 7` on 64-bit words.  The
compiler's theorem gives the module's correctness, and the encoder's round trip carries it to
the bytes. -/

namespace Verified.Examples.Poly

open LeanExe.Pipeline Verified

/-- The Lean function. -/
def poly (a b c : UInt64) : UInt64 := a * b + c * c - 7

/-- `poly` in the source language. -/
def polyFunc : Func :=
  ⟨3, .bin .sub (.bin .add (.bin .mul (.var 0) (.var 1)) (.bin .mul (.var 2) (.var 2)))
    (.const 7)⟩

def module : Wasm.Module := compile [(polyFunc, "poly")]

/-- `poly` with its three arguments as one tuple. -/
def polyTuple (x : UInt64 × UInt64 × UInt64) : UInt64 := poly x.1 x.2.1 x.2.2

/-- The source function means `poly`. -/
theorem polyFunc_denote (a b c : UInt64) : polyFunc.denote #v[a, b, c] = poly a b c := rfl

/-- The arguments of `polyFunc` from a tuple. -/
def args (x : UInt64 × UInt64 × UInt64) : Vector UInt64 polyFunc.arity := #v[x.1, x.2.1, x.2.2]

theorem poly_implements : ImplementsPureA false module 2 polyTuple := by
  have h : ImplementsPureA false module 2 polyFunc.denote :=
    Func.correct [(polyFunc, "poly")] 0 polyFunc "poly" rfl rfl
  have hComp : polyFunc.denote ∘ args = polyTuple := by
    funext x
    exact polyFunc_denote x.1 x.2.1 x.2.2
  rw [← hComp]
  exact ImplementsPureA.comap h args fun _ => rfl

/-- `encode` succeeds on `module`, and the module that `decode` reads from the bytes computes
`poly` on every input, without a trap. -/
theorem poly_bytes : ∃ bytes, Wasm.Encoding.encode module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ ImplementsPureA false m 2 polyTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip module (by decide) (by decide +kernel)
  exact ⟨bytes, success, module, decoded, poly_implements⟩

end Verified.Examples.Poly
