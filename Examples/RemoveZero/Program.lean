import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop

/-!
Main's Demo 12 in this dialect: an array of at most eight words without its first zero, in order,
or the input when it has no zero, or the empty array for a longer input.  `firstZero` is the index
of the first zero among the first `count` elements, or `count` when there is none, and the result
copies the elements before that index and shifts the rest down by one.
-/

namespace Examples.RemoveZero

def firstZero (xs : Array UInt64) (count : UInt64) : UInt64 :=
  LeanExe.loop count count fun i k => if k == count && xs[i.toNat]! == 0 then i else k

def compute (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  let count := if n ≤ 8 then n else 0
  let k := firstZero xs count
  LeanExe.build (if k < count then count - 1 else count) fun i =>
    if i < k then xs[i.toNat]! else xs[(i + 1).toNat]!

end Examples.RemoveZero
