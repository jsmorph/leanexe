import Verified.Reflect.Command

/-! The tenth program of the verified compiler: in-place updates with `xs.set! i.toNat v`.  The
array operand is owned and dies at the update when it comes from a `build`, a `let` of an owned
value, or a loop's state, and the update then writes into its block.  An array parameter is
borrowed, and an array that stays live after the update is copied first.  A position past the end
leaves the array unchanged, as Lean's `set!` does. -/

namespace Verified.Examples.Updates

def setParam (xs : Array UInt64) (i v : UInt64) : Array UInt64 := xs.set! i.toNat v

def setBuilt (n i v : UInt64) : Array UInt64 :=
  (LeanExe.build n fun j => j).set! i.toNat v

def swapEnds (xs : Array UInt64) : Array UInt64 :=
  let ys := LeanExe.build xs.size.toUInt64 fun j => xs[j.toNat]!
  let last := ys.size.toUInt64 - 1
  (ys.set! (0 : UInt64).toNat ys[last.toNat]!).set! last.toNat ys[(0 : UInt64).toNat]!

def histogram (xs : Array UInt64) (buckets : UInt64) : Array UInt64 :=
  LeanExe.loop xs.size.toUInt64 (LeanExe.build buckets fun _ => 0) fun i counts =>
    let b := xs[i.toNat]! % buckets
    counts.set! b.toNat (counts[b.toNat]! + 1)

def keepBoth (n i v : UInt64) : Array UInt64 × Array UInt64 :=
  let ys := LeanExe.build n fun j => j * 10
  (ys.set! i.toNat v, ys)

verified_compile compiled := [setParam, setBuilt, swapEnds, histogram, keepBoth]

end Verified.Examples.Updates
