import Library.Sorting.Insertion.Program
import Library.Arrays.Filter.Program
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

export Library.Sorting.Insertion (sortInsert)

export Library.Arrays.Filter (removeAll)

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

/-- An insertion into and a removal from a local array of pairs, two words per element, read back
as a weighted total of the words. -/
def pointTotal (n i : UInt64) (x : Float) (k : UInt64) : UInt64 :=
  let ps : Array (Float × UInt64) := LeanExe.build n fun j => (j.toFloat, j)
  let qs := LeanExe.eraseAt (LeanExe.insertAt ps i (x, k)) (i + 1)
  LeanExe.loop qs.size.toUInt64 0 fun j t => t + qs[j.toNat]!.2 * (j + 1)

def insertConserved (us : Array Conserved) (i : UInt64) (u : Conserved) : Array Conserved :=
  LeanExe.insertAt us i u

def eraseConserved (us : Array Conserved) (i : UInt64) : Array Conserved := LeanExe.eraseAt us i

/-- `n` copies of `u` pushed onto a built array of structures, a loop state whose credit is that of
a flattened array. -/
def pushConserved (n : UInt64) (u : Conserved) : Array Conserved :=
  LeanExe.loop n (LeanExe.build 0 fun _ => u) fun _ acc => acc.push u

verified_compile compiled := [insertParam, eraseParam, insertBuilt, eraseBuilt, insertKeep,
  Library.Sorting.Insertion.sortInsert, Library.Arrays.Filter.removeAll, pointTotal, insertConserved, eraseConserved, pushConserved]

/-- `sortInsert` inserts at most `xs.size` elements into a paid loop state, at a header and four
times the 8 added bytes each, after the built array's block and its credit. -/
theorem sortInsert_bound (xs : Array UInt64) :
    compiled.sortInsert.bound xs ≤ 72 + 80 * xs.size := by
  rw [compiled.sortInsert.bound_eq, loopCost_const]
  simp only [LeanExe.build, Array.size_ofFn, blockCost_eq, creditCost, paidGrowCost_eq,
    UInt64.toNat_zero, Nat.toUInt64, UInt64.toNat_ofNat']
  have := Nat.mod_le xs.size (2 ^ 64)
  omega

/-- `pushConserved` pushes `n` structures of three words onto a paid loop state, at a header and
four times the 24 added bytes each, after the built array's block and its credit. -/
theorem pushConserved_bound (n : UInt64) (u : Conserved) :
    compiled.pushConserved.bound (n, u) = 72 + 144 * n.toNat := by
  rw [compiled.pushConserved.bound_eq, loopCost_const]
  simp only [LeanExe.build, Array.size_ofFn, blockCost_eq, creditCost, paidGrowCost_eq,
    UInt64.toNat_zero]
  omega

end Verified.Examples.Insert
