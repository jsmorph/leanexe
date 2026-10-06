import Verified.Correct
import LeanExe.Encoding.RoundTrip

/-! The fourth program of the verified compiler: comparisons, `Bool` operations, `Bool`-valued
`let` bindings, conditionals, and a function that returns a `Bool`. -/

namespace Verified.Examples.Select

open LeanExe.Pipeline Verified

/-- The Lean functions.  `median` returns the middle of three words. -/
def median (a b c : UInt64) : UInt64 :=
  let ab : Bool := a ≤ b
  let bc : Bool := b ≤ c
  let ac : Bool := a ≤ c
  if (ab && bc) || (!ab && !bc) then b
  else if (ac && !bc) || (!ac && bc) then c
  else a

def inBand (x lo hi : UInt64) : Bool := (lo ≤ x && x < hi) || (x == hi && lo != hi)

/-- `median` in the source language.  Inside the three bindings, variables 0 to 5 are `ac`,
`bc`, `ab`, `a`, `b`, and `c`. -/
def medianFunc : Func S :=
  ⟨"median", [.word, .word, .word], .word,
    .letE (.cmp .le (.v 0) (.v 1))
      (.letE (.cmp .le (.v 2) (.v 3))
        (.letE (.cmp .le (.v 2) (.v 4))
          (.ite (.or (.and (.v 2) (.v 1)) (.and (.not (.v 2)) (.not (.v 1)))) (.v 4)
            (.ite (.or (.and (.v 0) (.not (.v 1))) (.and (.not (.v 0)) (.v 1))) (.v 5)
              (.v 3)))))⟩

/-- `inBand` in the source language: variables 0 to 2 are `x`, `lo`, and `hi`. -/
def inBandFunc : Func S :=
  ⟨"inBand", [.word, .word, .word], .bool,
    .or (.and (.cmp .le (.v 1) (.v 0)) (.cmp .lt (.v 0) (.v 2)))
      (.and (.cmp .eq (.v 0) (.v 2)) (.cmp .ne (.v 1) (.v 2)))⟩

/-- `median` is function 2 of the module, and `inBand` function 3. -/
def prog : Prog [([.word, .word, .word], .bool), ([.word, .word, .word], .word)] :=
  .cons inBandFunc (.cons medianFunc .nil)

def module : Wasm.Module := compile prog

def medianTuple (x : UInt64 × UInt64 × UInt64) : UInt64 := median x.1 x.2.1 x.2.2

def inBandTuple (x : UInt64 × UInt64 × UInt64) : Bool := inBand x.1 x.2.1 x.2.2

/-- The source functions mean `median` and `inBand`. -/
theorem medianFunc_denote (a b c : UInt64) :
    (medianFunc (S := [])).denote .nil (.cons a (.cons b (.cons c .nil))) = median a b c := rfl

theorem inBandFunc_denote (a b c : UInt64) :
    (inBandFunc (S := [])).denote .nil (.cons a (.cons b (.cons c .nil))) = inBand a b c := rfl

/-- The arguments of a function of three words from a tuple. -/
def args (x : UInt64 × UInt64 × UInt64) : Env [.word, .word, .word] :=
  .cons x.1 (.cons x.2.1 (.cons x.2.2 .nil))

theorem median_implements : ImplementsPureA false module 2 medianTuple := by
  have h : ImplementsPureA false module 2 ((medianFunc (S := [])).denote .nil) :=
    (Prog.correct prog (.there .here)).1
  have hComp : (medianFunc (S := [])).denote .nil ∘ args = medianTuple := by
    funext x
    exact medianFunc_denote x.1 x.2.1 x.2.2
  rw [← hComp]
  exact ImplementsPureA.comap h args fun _ => rfl

theorem inBand_implements : ImplementsPureA false module 3 inBandTuple := by
  have h : ImplementsPureA false module 3
      ((inBandFunc (S := [([.word, .word, .word], .word)])).denote
        (.cons ((medianFunc (S := [])).denote .nil) .nil)) :=
    (Prog.correct prog .here).1
  have hComp : (inBandFunc (S := [([.word, .word, .word], .word)])).denote
      (.cons ((medianFunc (S := [])).denote .nil) .nil) ∘ args = inBandTuple := by
    funext x
    exact inBandFunc_denote x.1 x.2.1 x.2.2
  rw [← hComp]
  exact ImplementsPureA.comap h args fun _ => rfl

/-- `encode` succeeds on `module`, and the module that `decode` reads from the bytes computes
`median` and `inBand` on every input, without a trap. -/
theorem select_bytes : ∃ bytes, Wasm.Encoding.encode module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ ImplementsPureA false m 2 medianTuple ∧
      ImplementsPureA false m 3 inBandTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip module (by decide) (by decide +kernel)
  exact ⟨bytes, success, module, decoded, median_implements, inBand_implements⟩

end Verified.Examples.Select
