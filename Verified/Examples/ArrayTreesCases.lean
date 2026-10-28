import Verified.Examples.ArrayTrees
import TestSupport.Host

/-! The cases of the trees whose records hold arrays.  Each case passes an array of words and a
word and returns a word, and the code builds, copies, updates, and consumes the trees in between.
The block count of each case is 1, the host's array: every record and every array that the code
allocates is released before the function returns. -/

namespace Verified.Examples.ArrayTrees

open TestSupport.Host

def arrayArg (xs : Array UInt64) : String :=
  "array-u64:" ++ ",".intercalate (xs.toList.map toString)

def cases : IO Unit := do
  let arrays : List (Array UInt64) := [#[], #[7], #[1, 2], #[maxU, 0, maxU],
    (List.range 9).toArray.map UInt64.ofNat, (List.range 300).toArray.map UInt64.ofNat] ++
    (List.range 12).map fun i => (List.range (3 * i)).toArray.map fun j => rw (17 * i + j)
  for xs in arrays do
    for x in [0, 5, maxU] do
      IO.println s!"arraytrees|grown|i64|{arrayArg xs} i64:{x}|{grown xs x}|1"
      IO.println s!"arraytrees|grownRoot|i64|{arrayArg xs} i64:{x}|{grownRoot xs x}|1"

end Verified.Examples.ArrayTrees
