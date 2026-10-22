import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile
import LeanExe.Dialect.InsertErase

namespace Library.Arrays.Filter

/-- The array without the elements equal to `v`, removed one at a time from the first. -/
def removeAll (xs : Array UInt64) (v : UInt64) : Array UInt64 :=
  LeanExe.loop xs.size.toUInt64 xs fun _ acc =>
    let n := acc.size.toUInt64
    let k := LeanExe.loop n n fun j k => if k == n && acc[j.toNat]! == v then j else k
    LeanExe.eraseAt acc k

/-- The elements of `xs` below `limit`, in order, gathered until `count` of them are found. -/
def below (xs : Array UInt64) (limit count : UInt64) : Array UInt64 :=
  (LeanExe.repeatWhile xs.size.toUInt64 ((0 : UInt64), LeanExe.build 0 fun i => i)
    (fun s => s.2.size.toUInt64 < count)
    fun s => (s.1 + 1, if xs[s.1.toNat]! < limit then s.2.push xs[s.1.toNat]! else s.2)).2

/-- `xs` with its elements set to 0 from the start up to the first element equal to `v`, in
place. -/
def clearUntil (xs : Array UInt64) (v : UInt64) : Array UInt64 :=
  (LeanExe.repeatWhile xs.size.toUInt64 ((0 : UInt64), xs)
    (fun s => s.1 < s.2.size.toUInt64 && s.2[s.1.toNat]! != v)
    fun s => (s.1 + 1, s.2.set! s.1.toNat 0)).2

end Library.Arrays.Filter
