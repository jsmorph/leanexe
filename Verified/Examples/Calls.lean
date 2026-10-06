import Verified.Correct
import LeanExe.Encoding.RoundTrip

/-! The fifth program of the verified compiler: four functions, each of which may call the
functions before it, with a call as the argument of another call and a call that returns a
`Bool` as the test of an `if`. -/

namespace Verified.Examples.Calls

open LeanExe.Pipeline Verified

/-- The Lean functions. -/
def sq (x : UInt64) : UInt64 := x * x

def sumSq (a b : UInt64) : UInt64 := sq a + sq b

def small (x : UInt64) : Bool := x < 100

def pick (a b c : UInt64) : UInt64 := if small a then sumSq (sumSq a b) c else sq (b - c)

abbrev sqSig : Sig := ([.word], .word)
abbrev sumSqSig : Sig := ([.word, .word], .word)
abbrev smallSig : Sig := ([.word], .bool)

def sqFunc : Func S := ⟨"sq", [.word], .word, .bin .mul (.v 0) (.v 0)⟩

/-- `sumSq` calls function 0 of its list, `sq`. -/
def sumSqFunc : Func [sqSig] :=
  ⟨"sumSq", [.word, .word], .word,
    .bin .add (.app 0 (.cons (.v 0) .nil)) (.app 0 (.cons (.v 1) .nil))⟩

def smallFunc : Func S := ⟨"small", [.word], .bool, .cmp .lt (.v 0) (.word 100)⟩

/-- `pick` calls functions 0 to 2 of its list: `small`, `sumSq`, and `sq`. -/
def pickFunc : Func [smallSig, sumSqSig, sqSig] :=
  ⟨"pick", [.word, .word, .word], .word,
    .ite (.app 0 (.cons (.v 0) .nil))
      (.app 1 (.cons (.app 1 (.cons (.v 0) (.cons (.v 1) .nil))) (.cons (.v 2) .nil)))
      (.app 2 (.cons (.bin .sub (.v 1) (.v 2)) .nil))⟩

/-- The module holds `sq`, `sumSq`, `small`, and `pick` as functions 2 to 5. -/
def prog : Prog [([.word, .word, .word], .word), smallSig, sumSqSig, sqSig] :=
  .cons pickFunc (.cons smallFunc (.cons sumSqFunc (.cons sqFunc .nil)))

def module : Wasm.Module := compile prog

/-- The program's functions mean the Lean functions. -/
theorem sq_denote (x : UInt64) : prog.funs.get (.there (.there (.there .here))) (.cons x .nil) =
    sq x := rfl

theorem sumSq_denote (a b : UInt64) :
    prog.funs.get (.there (.there .here)) (.cons a (.cons b .nil)) = sumSq a b := rfl

theorem small_denote (x : UInt64) : prog.funs.get (.there .here) (.cons x .nil) = small x := rfl

theorem pick_denote (a b c : UInt64) :
    prog.funs.get .here (.cons a (.cons b (.cons c .nil))) = pick a b c := rfl

def sumSqPair (x : UInt64 × UInt64) : UInt64 := sumSq x.1 x.2

def pickTuple (x : UInt64 × UInt64 × UInt64) : UInt64 := pick x.1 x.2.1 x.2.2

theorem sq_implements : ImplementsPureA false module 2 sq := by
  have h := (Prog.correct prog (.there (.there (.there .here)))).1
  have hComp : prog.funs.get (.there (.there (.there .here))) ∘ (fun x => .cons x .nil) = sq := by
    funext x
    exact sq_denote x
  rw [← hComp]
  exact ImplementsPureA.comap h _ fun _ => rfl

theorem sumSq_implements : ImplementsPureA false module 3 sumSqPair := by
  have h := (Prog.correct prog (.there (.there .here))).1
  have hComp : prog.funs.get (.there (.there .here)) ∘
      (fun x : UInt64 × UInt64 => .cons x.1 (.cons x.2 .nil)) = sumSqPair := by
    funext x
    exact sumSq_denote x.1 x.2
  rw [← hComp]
  exact ImplementsPureA.comap h _ fun _ => rfl

theorem small_implements : ImplementsPureA false module 4 small := by
  have h := (Prog.correct prog (.there .here)).1
  have hComp : prog.funs.get (.there .here) ∘ (fun x => .cons x .nil) = small := by
    funext x
    exact small_denote x
  rw [← hComp]
  exact ImplementsPureA.comap h _ fun _ => rfl

theorem pick_implements : ImplementsPureA false module 5 pickTuple := by
  have h := (Prog.correct prog .here).1
  have hComp : prog.funs.get .here ∘
      (fun x : UInt64 × UInt64 × UInt64 => .cons x.1 (.cons x.2.1 (.cons x.2.2 .nil))) =
        pickTuple := by
    funext x
    exact pick_denote x.1 x.2.1 x.2.2
  rw [← hComp]
  exact ImplementsPureA.comap h _ fun _ => rfl

/-- `encode` succeeds on `module`, and the module that `decode` reads from the bytes computes the
four Lean functions on every input, without a trap. -/
theorem calls_bytes : ∃ bytes, Wasm.Encoding.encode module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ ImplementsPureA false m 2 sq ∧
      ImplementsPureA false m 3 sumSqPair ∧ ImplementsPureA false m 4 small ∧
      ImplementsPureA false m 5 pickTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip module (by decide) (by decide +kernel)
  exact ⟨bytes, success, module, decoded, sq_implements, sumSq_implements, small_implements,
    pick_implements⟩

end Verified.Examples.Calls
