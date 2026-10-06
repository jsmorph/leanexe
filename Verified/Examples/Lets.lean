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

/-- `scramble` in the source language.  Each `letE` puts its value at variable 0: inside the
innermost binding, variables 0 to 5 are `w`, `z`, `y`, `x`, `a`, and `b`. -/
def scrambleFunc : Func S :=
  ⟨"scramble", [.word, .word], .word,
    .letE (.bin .xor (.v 0) (.bin .shl (.v 1) (.word 13)))
      (.letE (.bin .mul (.v 0) (.word 0x9e3779b97f4a7c15))
        (.letE (.bin .xor (.v 0) (.bin .shr (.v 0) (.word 29)))
          (.bin .add
            (.letE (.bin .or (.v 4) (.word 1)) (.bin .div (.v 1) (.bin .mul (.v 0) (.v 0))))
            (.bin .rem (.v 0) (.bin .add (.v 3) (.word 7))))))⟩

def prog : Prog [([.word, .word], .word)] := .cons scrambleFunc .nil

def module : Wasm.Module := compile prog

/-- `scramble` with its two arguments as one pair. -/
def scramblePair (x : UInt64 × UInt64) : UInt64 := scramble x.1 x.2

/-- The source function means `scramble`. -/
theorem scrambleFunc_denote (a b : UInt64) :
    (scrambleFunc (S := [])).denote .nil (.cons a (.cons b .nil)) = scramble a b := rfl

/-- The arguments of `scrambleFunc` from a pair. -/
def args (x : UInt64 × UInt64) : Env [.word, .word] := .cons x.1 (.cons x.2 .nil)

theorem scramble_implements : ImplementsPureA false module 2 scramblePair := by
  have h : ImplementsPureA false module 2 ((scrambleFunc (S := [])).denote .nil) :=
    (Prog.correct prog .here).1
  have hComp : (scrambleFunc (S := [])).denote .nil ∘ args = scramblePair := by
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
