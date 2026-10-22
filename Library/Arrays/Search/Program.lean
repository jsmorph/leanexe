import LeanExe.Dialect.Loop

namespace Library.Arrays.Search

def count (xs : Array UInt64) (key : UInt64) : UInt64 :=
  LeanExe.loop xs.size.toUInt64 0 fun i acc => if xs[i.toNat]! == key then acc + 1 else acc

def firstAbove (xs : Array UInt64) (limit : UInt64) : UInt64 × Bool :=
  LeanExe.loop xs.size.toUInt64 ((0 : UInt64), false) fun i (found, seen) =>
    if seen then (found, seen) else if limit < xs[i.toNat]! then (i, true) else (found, seen)

def firstZero (xs : Array UInt64) (count : UInt64) : UInt64 :=
  LeanExe.loop count count fun i k => if k == count && xs[i.toNat]! == 0 then i else k

end Library.Arrays.Search
