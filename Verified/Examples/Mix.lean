import Verified.Correct
import LeanExe.Encoding.RoundTrip

/-! The second program of the verified compiler: division, remainder, the bitwise operations, and
both shifts on 64-bit words, with Lean's results for a zero divisor and for shift amounts of 64
or more. -/

namespace Verified.Examples.Mix

open LeanExe.Pipeline Verified

/-- The Lean function. -/
def mix (a b c : UInt64) : UInt64 := ((a / b + a % c) ^^^ ((a &&& b) ||| (c <<< b))) - (a >>> c)

/-- `mix` in the source language. -/
def mixFunc : Func S :=
  ⟨"mix", [.word, .word, .word], .word, .bin .sub
    (.bin .xor (.bin .add (.bin .div (.v 0) (.v 1)) (.bin .rem (.v 0) (.v 2)))
      (.bin .or (.bin .and (.v 0) (.v 1)) (.bin .shl (.v 2) (.v 1))))
    (.bin .shr (.v 0) (.v 2))⟩

def prog : Prog [([.word, .word, .word], .word)] := .cons mixFunc .nil

def module : Wasm.Module := compile prog

/-- `mix` with its three arguments as one tuple. -/
def mixTuple (x : UInt64 × UInt64 × UInt64) : UInt64 := mix x.1 x.2.1 x.2.2

/-- The source function means `mix`. -/
theorem mixFunc_denote (a b c : UInt64) :
    (mixFunc (S := [])).denote .nil (.cons a (.cons b (.cons c .nil))) = mix a b c := rfl

/-- The arguments of `mixFunc` from a tuple. -/
def args (x : UInt64 × UInt64 × UInt64) : Env [.word, .word, .word] :=
  .cons x.1 (.cons x.2.1 (.cons x.2.2 .nil))

theorem mix_implements : ImplementsPureA false module 2 mixTuple := by
  have h : ImplementsPureA false module 2 ((mixFunc (S := [])).denote .nil) :=
    (Prog.correct prog .here).1
  have hComp : (mixFunc (S := [])).denote .nil ∘ args = mixTuple := by
    funext x
    exact mixFunc_denote x.1 x.2.1 x.2.2
  rw [← hComp]
  exact ImplementsPureA.comap h args fun _ => rfl

/-- `encode` succeeds on `module`, and the module that `decode` reads from the bytes computes
`mix` on every input, without a trap. -/
theorem mix_bytes : ∃ bytes, Wasm.Encoding.encode module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ ImplementsPureA false m 2 mixTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip module (by decide) (by decide +kernel)
  exact ⟨bytes, success, module, decoded, mix_implements⟩

end Verified.Examples.Mix
