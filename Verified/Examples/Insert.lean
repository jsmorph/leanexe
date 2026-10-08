import Verified.Examples.Records

/-! The twenty-fifth program of the verified compiler: `LeanExe.insertAt` and `LeanExe.eraseAt`.
An insertion takes the array with room for one more element, as `push` does, and moves the
elements from the position on up by one element, and a removal moves the elements after the
position down by one element and shortens the array.  An owned array that dies at the operation
changes in its own block, and any other array is copied first.  A parameter that dies at the
operation is owned, so the function changes the caller's array in its block.  A position past the end leaves
the array unchanged.  The programs insert into and remove from parameters, built arrays, a loop's
state, a local array of pairs, and arrays of structures. -/

namespace Verified.Examples.Insert

open Verified.Examples.Records

def insertParam (xs : Array UInt64) (i v : UInt64) : Array UInt64 := LeanExe.insertAt xs i v

def eraseParam (xs : Array UInt64) (i : UInt64) : Array UInt64 := LeanExe.eraseAt xs i

def insertBuilt (n i v : UInt64) : Array UInt64 :=
  LeanExe.insertAt (LeanExe.build n fun j => j) i v

def eraseBuilt (n i : UInt64) : Array UInt64 := LeanExe.eraseAt (LeanExe.build n fun j => j) i

/-- An insertion that keeps the array it inserts into, which it therefore copies. -/
def insertKeep (n i v : UInt64) : Array UInt64 × Array UInt64 :=
  let ys := LeanExe.build n fun j => j
  (LeanExe.insertAt ys i v, ys)

/-- Insertion sort: each value goes in at the number of smaller values before it, in a loop whose
state grows in its own block. -/
def sortInsert (xs : Array UInt64) : Array UInt64 :=
  LeanExe.loop xs.size.toUInt64 (LeanExe.build 0 fun _ => 0) fun i acc =>
    let v := xs[i.toNat]!
    let k := LeanExe.loop acc.size.toUInt64 0 fun j c => if acc[j.toNat]! < v then c + 1 else c
    LeanExe.insertAt acc k v

/-- The array without the elements equal to `v`, removed one at a time from the first. -/
def removeAll (xs : Array UInt64) (v : UInt64) : Array UInt64 :=
  LeanExe.loop xs.size.toUInt64 xs fun _ acc =>
    let n := acc.size.toUInt64
    let k := LeanExe.loop n n fun j k => if k == n && acc[j.toNat]! == v then j else k
    LeanExe.eraseAt acc k

/-- An insertion into and a removal from a local array of pairs, two words per element, read back
as a weighted total of the words. -/
def pointTotal (n i : UInt64) (x : Float) (k : UInt64) : UInt64 :=
  let ps : Array (Float × UInt64) := LeanExe.build n fun j => (j.toFloat, j)
  let qs := LeanExe.eraseAt (LeanExe.insertAt ps i (x, k)) (i + 1)
  LeanExe.loop qs.size.toUInt64 0 fun j t => t + qs[j.toNat]!.2 * (j + 1)

def insertConserved (us : Array Conserved) (i : UInt64) (u : Conserved) : Array Conserved :=
  LeanExe.insertAt us i u

def eraseConserved (us : Array Conserved) (i : UInt64) : Array Conserved := LeanExe.eraseAt us i

verified_compile compiled := [insertParam, eraseParam, insertBuilt, eraseBuilt, insertKeep,
  sortInsert, removeAll, pointTotal, insertConserved, eraseConserved]

end Verified.Examples.Insert
