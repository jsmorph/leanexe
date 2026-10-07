import Verified.Reflect.Command

/-! The eighth program of the verified compiler: arrays of words as parameters, read with
`xs.size.toUInt64` and the bounds-checked `xs[i.toNat]!`, inside loops, passed to calls, bound with
`let`, and held in a pair.  An array is passed as its address and borrowed, so no function here
allocates, and every function returns without a trap. -/

namespace Verified.Examples.Arrays

def sum (xs : Array UInt64) : UInt64 :=
  LeanExe.loop xs.size.toUInt64 0 fun i acc => acc + xs[i.toNat]!

def dot (xs ys : Array UInt64) : UInt64 :=
  LeanExe.loop xs.size.toUInt64 0 fun i acc => acc + xs[i.toNat]! * ys[i.toNat]!

def count (xs : Array UInt64) (key : UInt64) : UInt64 :=
  LeanExe.loop xs.size.toUInt64 0 fun i acc => if xs[i.toNat]! == key then acc + 1 else acc

def firstAbove (xs : Array UInt64) (limit : UInt64) : UInt64 × Bool :=
  LeanExe.loop xs.size.toUInt64 ((0 : UInt64), false) fun i (found, seen) =>
    if seen then (found, seen) else if limit < xs[i.toNat]! then (i, true) else (found, seen)

def at3 (xs : Array UInt64) (i : UInt64) : UInt64 := xs[i.toNat]! + xs[(i + 1).toNat]!

def sumBoth (p : Array UInt64 × Array UInt64) : UInt64 := sum p.1 + sum p.2

def larger (xs ys : Array UInt64) : UInt64 :=
  let zs := if xs.size.toUInt64 ≤ ys.size.toUInt64 then ys else xs
  sum zs + zs.size.toUInt64

verified_compile compiled := [sum, dot, count, firstAbove, at3, sumBoth, larger]

end Verified.Examples.Arrays
