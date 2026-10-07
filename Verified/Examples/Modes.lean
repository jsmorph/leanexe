import Verified.Reflect.Command

/-! The twelfth program of the verified compiler: parameter modes.  The reflector makes an array
parameter owned when the body consumes it where it dies, and a caller then moves an owned
variable that dies at the call into the function instead of copying it.  A parameter that the
body reads, or uses again after the consuming use, stays borrowed.  `byHand` is a program written
without the reflector whose parameters are owned without such a use: one function never reads its
array parameter and releases it at entry, and the other reads it last with `size`, which releases
it. -/

namespace Verified.Examples.Modes

def same (xs : Array UInt64) : Array UInt64 := xs

def withCount (xs : Array UInt64) : UInt64 × Array UInt64 := (xs.size.toUInt64, xs)

def bump (xs : Array UInt64) (i : UInt64) : Array UInt64 := xs.set! i.toNat (xs[i.toNat]! + 1)

def bumpFirst (xs : Array UInt64) : Array UInt64 := bump xs 0

def bumpTwice (xs : Array UInt64) : Array UInt64 := bump (bump xs 0) 1

def bumpLast (xs : Array UInt64) : Array UInt64 := bump xs (xs.size.toUInt64 - 1)

def bumpAll (xs : Array UInt64) : Array UInt64 :=
  LeanExe.loop xs.size.toUInt64 xs fun i ys => bump ys i

def addSelf (xs : Array UInt64) : Array UInt64 := xs ++ xs

def sizes (p : Array UInt64 × Array UInt64) : UInt64 := p.1.size.toUInt64 + p.2.size.toUInt64

def pairArg (xs : Array UInt64) : UInt64 × Array UInt64 := (sizes (xs, xs), xs)

def swapPair (p : Array UInt64 × Array UInt64) : Array UInt64 × Array UInt64 := (p.2, p.1)

def both (xs ys : Array UInt64) : Array UInt64 × Array UInt64 := (xs, ys)

def twoSame (xs : Array UInt64) : Array UInt64 × Array UInt64 := both xs xs

def bumpKeep (xs : Array UInt64) : Array UInt64 × Array UInt64 := (bump xs 0, xs)

verified_compile compiled := [same, withCount, bump, bumpFirst, bumpTwice, bumpLast, bumpAll,
  addSelf, sizes, pairArg, swapPair, both, twoSame, bumpKeep]

/-- The theorem for an owned array parameter takes the argument as `Moved (Array UInt64)`. -/
example : LeanExe.Pipeline.ImplementsA true compiled.module 2
    (fun (x : LeanExe.Pipeline.Moved (Array UInt64)) => same x.val) (fun _ _ _ => True)
    (fun _ _ _ _ _ => True) :=
  compiled.same.implements

/-- `dropArg xs n = n`, with `xs` owned and never read. -/
def dropArg (S : List Sig) : Func S where
  name := "dropArg"
  params := [.array .word, .word]
  result := .word
  body := .var (.there .here)
  placeArgs := rfl
  modes := [.owned]

/-- `sizeOwned xs = xs.size`, with `xs` owned. -/
def sizeOwned (S : List Sig) : Func S where
  name := "sizeOwned"
  params := [.array .word]
  result := .word
  body := .size .here
  placeArgs := rfl
  modes := [.owned]

def byHand := Prog.cons (sizeOwned _) (Prog.cons (dropArg []) .nil)

def byHandModule : Wasm.Module := compile byHand

end Verified.Examples.Modes
