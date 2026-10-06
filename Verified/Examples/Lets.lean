import Verified.Correct
import LeanExe.Encoding.RoundTrip

/-! The third program of the verified compiler: `let` bindings, including one inside the operand
of a division, whose locals sit above the division's scratch locals. -/

namespace Verified.Examples.Lets

open LeanExe.Pipeline Verified

/-- The Lean function. -/
def scramble (a b : UInt64) : UInt64 :=
  let x := a ^^^ (b <<< 13)
  let y := x * 0x9e3779b97f4a7c15
  let z := y ^^^ (y >>> 29)
  (let w := b ||| 1; z / (w * w)) + z % (a + 7)

/-- `scramble` in the source language: variables 0 and 1 are `a` and `b`, and 2 to 5 are `x`,
`y`, `z`, and `w`. -/
def scrambleFunc : Func :=
  ⟨2, .letE (.bin .xor (.var 0) (.bin .shl (.var 1) (.const 13)))
    (.letE (.bin .mul (.var 2) (.const 0x9e3779b97f4a7c15))
      (.letE (.bin .xor (.var 3) (.bin .shr (.var 3) (.const 29)))
        (.bin .add
          (.letE (.bin .or (.var 1) (.const 1)) (.bin .div (.var 4) (.bin .mul (.var 5) (.var 5))))
          (.bin .rem (.var 4) (.bin .add (.var 0) (.const 7))))))⟩

def module : Wasm.Module := compile [(scrambleFunc, "scramble")]

/-- `scramble` with its two arguments as one pair. -/
def scramblePair (x : UInt64 × UInt64) : UInt64 := scramble x.1 x.2

/-- The source function means `scramble`. -/
theorem scrambleFunc_denote (a b : UInt64) : scrambleFunc.denote #v[a, b] = scramble a b := rfl

/-- The arguments of `scrambleFunc` from a pair. -/
def args (x : UInt64 × UInt64) : Vector UInt64 scrambleFunc.arity := #v[x.1, x.2]

theorem scramble_implements : ImplementsPureA false module 2 scramblePair := by
  have h : ImplementsPureA false module 2 scrambleFunc.denote :=
    Func.correct [(scrambleFunc, "scramble")] 0 scrambleFunc "scramble" rfl rfl
  have hComp : scrambleFunc.denote ∘ args = scramblePair := by
    funext x
    exact scrambleFunc_denote x.1 x.2
  rw [← hComp]
  exact ImplementsPureA.comap h args fun _ => rfl

/-- `encode` succeeds on `module`, and the module that `decode` reads from the bytes computes
`scramble` on every input, without a trap. -/
theorem scramble_bytes : ∃ bytes, Wasm.Encoding.encode module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ ImplementsPureA false m 2 scramblePair := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip module (by decide) (by decide +kernel)
  exact ⟨bytes, success, module, decoded, scramble_implements⟩

end Verified.Examples.Lets
