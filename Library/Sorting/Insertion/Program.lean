import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.InsertErase

namespace Library.Sorting.Insertion

/-- Insertion sort: each value goes in at the number of smaller values before it, in a loop whose
state grows in its own block. -/
def sortInsert (xs : Array UInt64) : Array UInt64 :=
  LeanExe.loop xs.size.toUInt64 (LeanExe.build 0 fun _ => 0) fun i acc =>
    let v := xs[i.toNat]!
    let k := LeanExe.loop acc.size.toUInt64 0 fun j c => if acc[j.toNat]! < v then c + 1 else c
    LeanExe.insertAt acc k v

end Library.Sorting.Insertion
