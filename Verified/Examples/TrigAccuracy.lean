import Verified.Examples.Trig

/-! A native check of `Trig.sin` and `Trig.cos` against the C library's `sin` and `cos`, which
Lean's `Float.sin` and `Float.cos` call, glibc's on Linux.  fdlibm and glibc each state an error
below one unit in the last place, so two such results lie at most one unit apart.  The check
covers arguments below `2 ^ 20 · π/2` in magnitude, the range of the current reduction: hashed
values over the exponents from `2 ^ -30` up, evenly spaced values up to 100, and the doubles next
to `k · π/2` for `k` up to 20,000, where the reduction cancels.  It prints the largest distance
and exits with an error at the first pair of results further apart, or at a NaN or infinity on one
side only.  Run with `lake env lean --run`. -/

namespace Verified.Examples.TrigAccuracy

/-- The position of a finite float among the floats in order. -/
def order (x : Float) : Int :=
  let b := x.toBits
  if b >>> 63 == 1 then -((b &&& 0x7FFFFFFFFFFFFFFF).toNat : Int) else (b.toNat : Int)

/-- The number of floats from `a` to `b`, when both are finite or both are the same non-finite
value. -/
def distance (a b : Float) : Option Nat :=
  if a.isNaN || b.isNaN then if a.isNaN && b.isNaN then some 0 else none
  else if a.isInf || b.isInf then if a == b then some 0 else none
  else some (order a - order b).natAbs

/-- Whether `x` lies in the range of the current reduction. -/
def inRange (x : Float) : Bool := ((x.toBits >>> 32) &&& 0x7fffffff) < 0x413921fb

def args : Array Float :=
  let hashed := (Array.range 100000).map fun i =>
    let h := (UInt64.ofNat i + 7) * 0x9e3779b97f4a7c15
    let e : UInt64 := 993 + (h >>> (58 : UInt64)) % 52
    let x := Float.ofBits ((e <<< 52) ||| (h &&& 0xFFFFFFFFFFFFF))
    if h &&& 0x8000 == 0 then x else -x
  let even := (Array.range 20001).map fun i => (UInt64.ofNat i).toFloat * 0.005
  let multiples := (Array.range 20000).flatMap fun k =>
    let b := ((UInt64.ofNat (k + 1)).toFloat * 1.5707963267948966).toBits
    #[b - 1, b, b + 1].map Float.ofBits
  (hashed ++ even ++ multiples).filter inRange

end Verified.Examples.TrigAccuracy

open Verified.Examples Verified.Examples.TrigAccuracy in
def main : IO UInt32 := do
  let mut worst := 0
  let mut count := 0
  let mut unequal := 0
  for x in args do
    for (name, ours, ref) in [("sin", Trig.sin x, Float.sin x), ("cos", Trig.cos x, Float.cos x)] do
      count := count + 1
      match distance ours ref with
      | none =>
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, the C library {ref.toBits}"
        return 1
      | some d =>
        if 1 < d then
          IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, the C library \
            {ref.toBits}, {d} units apart"
          return 1
        if 0 < d then unequal := unequal + 1
        worst := max worst d
  IO.println s!"trig accuracy: {count} results within {worst} unit of the C library's, \
    {unequal} of them unequal"
  return 0
