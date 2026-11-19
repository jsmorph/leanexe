import Verified.Reflect.Command

/-! A program of the verified compiler: a tuple parameter that holds an array and that the
function consumes.  The functions are written in the source language with the owned mode for the
pair.  Each body splits the pair at entry, which moves its words into the components' locals:
`pushPair` extends the array in place and returns it, and `countPair` reads its size last, which
releases it.  The theorem of each function takes its argument as
`Moved (Array UInt64 × UInt64)`, which the caller moves to the call, by the agreement of Lean's
instance for that type with the compiler's representation of an owned pair. -/

namespace Verified.Examples.OwnedTuples

open LeanExe.Pipeline

def pushPair (p : Array UInt64 × UInt64) : Array UInt64 := p.1.push p.2

def pushPairF (S : List Sig) : Func S where
  name := "pushPair"
  params := [.pair (.array .word) .word]
  result := .array .word
  body := .letPair (.var .here) (.push (Var.ofIndex _ 1 rfl) (.v 0))
  placeArgs := rfl
  modes := [.owned]

example (p : Array UInt64 × UInt64) : (pushPairF []).denote .nil (.cons p .nil) = pushPair p :=
  rfl

def countPair (p : Array UInt64 × UInt64) : UInt64 := p.1.size.toUInt64 + p.2

def countPairF (S : List Sig) : Func S where
  name := "countPair"
  params := [.pair (.array .word) .word]
  result := .word
  body := .letPair (.var .here) (.bin .add (.size (Var.ofIndex _ 1 rfl)) (.v 0))
  placeArgs := rfl
  modes := [.owned]

example (p : Array UInt64 × UInt64) : (countPairF []).denote .nil (.cons p .nil) = countPair p :=
  rfl

def prog := Prog.consSig (pushPairF _) <| Prog.consSig (countPairF _) .nil

def module : Wasm.Module := compile prog

/-- Every function of the module computes its meaning, by the compiler's theorem. -/
theorem correct :
    Calls module prog.funs prog.flags (prog.boundsAt prog.funs) (prog.fitsAt prog.funs)
      Bytes.LiteralPool.empty :=
  Prog.correct_funs prog rfl (by decide +kernel)

/-- `pushPair` at index 3 computes its Lean function on an argument that the caller moves: the
call consumes the pair's array. -/
theorem pushPair_implements :
    ImplementsA true module 3 (fun x : Moved (Array UInt64 × UInt64) => pushPair x.val)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  ImplementsA.transferAgree
    (ImplementsA.lean (ImplementsB.implementsA (FunSpec.implementsB (correct .here 0) rfl)))
    (fun x => x) id (fun x => pushPair x.val) (fun _ => rfl)
    (Agree.movedProd (Agree.refl instRepresentMovedArrayUInt64)
      (Agree.movedScalar id fun _ => rfl))
    (Agree.refl _)

/-- `countPair` at index 2 computes its Lean function on an argument that the caller moves. -/
theorem countPair_implements :
    ImplementsA true module 2 (fun x : Moved (Array UInt64 × UInt64) => countPair x.val)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  ImplementsA.transferAgree
    (ImplementsA.lean
      (ImplementsB.implementsA (FunSpec.implementsB (correct (.there .here) 0) rfl)))
    (fun x => x) id (fun x => countPair x.val) (fun _ => rfl)
    (Agree.movedProd (Agree.refl instRepresentMovedArrayUInt64)
      (Agree.movedScalar id fun _ => rfl))
    (Agree.refl _)

#print axioms pushPair_implements
#print axioms countPair_implements

end Verified.Examples.OwnedTuples
