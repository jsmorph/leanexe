import Verified.Reflect.Command

/-! The fifteenth program of the verified compiler: arrays of tuples, whose elements occupy
several consecutive words.  Lean has no `Represent` instance for an array of pairs, so the
reflector rejects such types as parameters and results, and the programs here are written in the
source language.  Each
`example` states that a source function means the Lean function beside it.  Arrays of structures
with `Flat` instances reach the same arrays through the reflector, in `Grids.lean`. -/

namespace Verified.Examples.Tuples

/-- An element of a float and a word. -/
abbrev P : Elem := .prod .float .word

/-- An element of a word and a `Bool`, then a float. -/
abbrev N : Elem := .prod (.prod .word .bool) .float

def points (n : UInt64) : Array (Float × UInt64) :=
  LeanExe.build n fun i => (i.toFloat, i * 3)

def pointsF (S : List Sig) : Func S where
  name := "points"
  params := [.word]
  result := .array P
  body := .build (.v 0) (.mk (.toFloat .convert (.v 0)) (.bin .mul (.v 0) (.word 3)))
  placeArgs := rfl
  modes := []

example (n : UInt64) : (pointsF []).denote .nil (.cons n .nil) = points n := rfl

def sumFirst (xs : Array (Float × UInt64)) : Float :=
  LeanExe.loop xs.size.toUInt64 (0 : UInt64).toFloat fun i acc => acc + xs[i.toNat]!.1

def sumFirstF (S : List Sig) : Func S where
  name := "sumFirst"
  params := [.array P]
  result := .float
  body := .loop (.size (Var.ofIndex _ 0 rfl)) (.toFloat .convert (.word 0)) (.bool true)
    (.fbin .add (.v 0)
      (.letE (.get (Var.ofIndex _ 2 rfl) (.v 1)) (.proj (Var.ofIndex _ 0 rfl) (.fst .here))))
  placeArgs := rfl
  modes := []

example (xs : Array (Float × UInt64)) :
    (sumFirstF []).denote .nil (.cons xs .nil) = sumFirst xs := rfl

/-- Element `i` with one added to each part, in place when `xs` is owned. -/
def bump (xs : Array (Float × UInt64)) (i : UInt64) : Array (Float × UInt64) :=
  let t := xs[i.toNat]!
  xs.set! i.toNat (t.1 + (1 : UInt64).toFloat, t.2 + 1)

def bumpF (S : List Sig) : Func S where
  name := "bump"
  params := [.array P, .word]
  result := .array P
  body := .letE (.get (Var.ofIndex _ 0 rfl) (.v 1))
    (.set (Var.ofIndex _ 1 rfl) (.v 2)
      (.mk (.fbin .add (.proj (Var.ofIndex _ 0 rfl) (.fst .here)) (.toFloat .convert (.word 1)))
        (.bin .add (.proj (Var.ofIndex _ 0 rfl) (.snd .here)) (.word 1))))
  placeArgs := rfl
  modes := [.owned]

example (xs : Array (Float × UInt64)) (i : UInt64) :
    (bumpF []).denote .nil (.cons xs (.cons i .nil)) = bump xs i := rfl

def pushPoint (xs : Array (Float × UInt64)) (x : Float) (k : UInt64) : Array (Float × UInt64) :=
  xs.push (x, k)

def pushPointF (S : List Sig) : Func S where
  name := "pushPoint"
  params := [.array P, .float, .word]
  result := .array P
  body := .push (Var.ofIndex _ 0 rfl) (.mk (.v 1) (.v 2))
  placeArgs := rfl
  modes := [.owned]

example (xs : Array (Float × UInt64)) (x : Float) (k : UInt64) :
    (pushPointF []).denote .nil (.cons xs (.cons x (.cons k .nil))) = pushPoint xs x k := rfl

def joined (xs ys : Array (Float × UInt64)) : Array (Float × UInt64) := xs ++ ys

def joinedF (S : List Sig) : Func S where
  name := "joined"
  params := [.array P, .array P]
  result := .array P
  body := .append (Var.ofIndex _ 0 rfl) (Var.ofIndex _ 1 rfl)
  placeArgs := rfl
  modes := [.owned]

example (xs ys : Array (Float × UInt64)) :
    (joinedF []).denote .nil (.cons xs (.cons ys .nil)) = joined xs ys := rfl

def count (xs : Array (Float × UInt64)) : UInt64 := xs.size.toUInt64

def countF (S : List Sig) : Func S where
  name := "count"
  params := [.array P]
  result := .word
  body := .size (Var.ofIndex _ 0 rfl)
  placeArgs := rfl
  modes := []

example (xs : Array (Float × UInt64)) : (countF []).denote .nil (.cons xs .nil) = count xs := rfl

def flags (n : UInt64) : Array ((UInt64 × Bool) × Float) :=
  LeanExe.build n fun i => ((i, i % 2 == 0), i.toFloat)

def flagsF (S : List Sig) : Func S where
  name := "flags"
  params := [.word]
  result := .array N
  body := .build (.v 0)
    (.mk (.mk (.v 0) (.cmp .eq (.bin .rem (.v 0) (.word 2)) (.word 0))) (.toFloat .convert (.v 0)))
  placeArgs := rfl
  modes := []

example (n : UInt64) : (flagsF []).denote .nil (.cons n .nil) = flags n := rfl

def flagAt (xs : Array ((UInt64 × Bool) × Float)) (i : UInt64) : Bool := xs[i.toNat]!.1.2

def flagAtF (S : List Sig) : Func S where
  name := "flagAt"
  params := [.array N, .word]
  result := .bool
  body := .letE (.get (Var.ofIndex _ 0 rfl) (.v 1))
    (.proj (Var.ofIndex _ 0 rfl) (.fst (.snd .here)))
  placeArgs := rfl
  modes := []

example (xs : Array ((UInt64 × Bool) × Float)) (i : UInt64) :
    (flagAtF []).denote .nil (.cons xs (.cons i .nil)) = flagAt xs i := rfl

def prog := Prog.cons (pointsF _) <| Prog.cons (sumFirstF _) <| Prog.cons (bumpF _) <|
  Prog.cons (pushPointF _) <| Prog.cons (joinedF _) <| Prog.cons (countF _) <|
  Prog.cons (flagsF _) <| Prog.cons (flagAtF _) .nil

def module : Wasm.Module := compile prog

/-- Every function of the module computes its meaning, by the compiler's theorem. -/
theorem correct : Calls module prog.funs (prog.boundsAt prog.funs) (prog.fitsAt prog.funs) :=
  Prog.correct_funs prog rfl

end Verified.Examples.Tuples
