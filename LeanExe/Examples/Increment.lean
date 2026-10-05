import LeanExe.Build

/-!
Main's Demo 4 in this dialect: each element of an array of at most eight words plus one, with
wrapping arithmetic, or the empty array for a longer input.  The count is 0 for a longer input,
so one build serves both cases.
-/

namespace LeanExe.Examples.Increment

def compute (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  let count := if n ≤ 8 then n else 0
  LeanExe.build count fun i => xs[i.toNat]! + 1

end LeanExe.Examples.Increment
