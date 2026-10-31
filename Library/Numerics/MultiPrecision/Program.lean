import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-! Multiple-precision arithmetic, Algorithms A, S, and M of TAOCP §4.3.1, on arrays of digits in
base `2^32`, least significant first.  A read `u[j]!` past the end of `u` gives 0, so the loops
read both arguments up to the larger length.  Each loop's state holds the word that the next step
reads first, the carry or the borrow, before the array that the step changes. -/

namespace Library.Numerics.MultiPrecision

/-- The larger of the lengths of `u` and `v`. -/
def width (u v : Array UInt64) : UInt64 :=
  if u.size.toUInt64 < v.size.toUInt64 then v.size.toUInt64 else u.size.toUInt64

/-- Algorithm A: the digits of `u + v`, with the final carry as the last digit. -/
def add (u v : Array UInt64) : Array UInt64 :=
  let s := LeanExe.loop (width u v) ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    ((u[j.toNat]! + v[j.toNat]! + s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + v[j.toNat]! + s.1) % 4294967296))
  s.2.push s.1

/-- Algorithm S: the digits of `u - v`, without the final borrow.  The step adds the base before
it subtracts, so that no word wraps, and the borrow is 1 when the sum stays below the base. -/
def sub (u v : Array UInt64) : Array UInt64 :=
  (LeanExe.loop (width u v) ((0 : UInt64), (#[] : Array UInt64)) fun j s =>
    (1 - (u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + 4294967296 - v[j.toNat]! - s.1) % 4294967296))).2

/-- Algorithm M: the digits of `u * v`.  For each digit `v[j]`, the inner loop adds `u * v[j]` to
the digits from position `j` on, and the last carry becomes digit `j + m`. -/
def mul (u v : Array UInt64) : Array UInt64 :=
  LeanExe.loop v.size.toUInt64
    (LeanExe.build (u.size.toUInt64 + v.size.toUInt64) fun _ => (0 : UInt64)) fun j w =>
    let s := LeanExe.loop u.size.toUInt64 ((0 : UInt64), w) fun i s =>
      ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) / 4294967296,
        s.2.set! (i + j).toNat ((u[i.toNat]! * v[j.toNat]! + s.2[(i + j).toNat]! + s.1) % 4294967296))
    s.2.set! (j + u.size.toUInt64).toNat s.1

end Library.Numerics.MultiPrecision
