import Examples.Updates.Program
import TestSupport.Host

/-! The module cases of `updates`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Updates

open TestSupport.Host

/-- The arguments `(xs, a)` of `pushTwo` and `pushCopy`, which the verified compiler's cases also
use: each array with four values that depend on its length. -/
def pushArgs : List (List UInt64 × UInt64) :=
  wordArrays.flatMap fun xs => ([0, 1, 2, 5] : List Nat).map fun i => (xs, rw (xs.length + i))

/-- The arguments `(xs, i, j, a)` of `setTwice` and `insertErase`, which the verified compiler's
cases also use: positions inside and past the end of each array. -/
def updateArgs : List (List UInt64 × UInt64 × UInt64 × UInt64) :=
  wordArrays.flatMap fun xs => ([0, 1, 2, 5] : List UInt64).flatMap fun i =>
    ([0, 1, 3, 7] : List UInt64).map fun j => (xs, i, j, rw (xs.length + i.toNat))

/-- Chains of updates and a borrowed `push`, at positions inside and past the end of each array. -/
def updatesCases : IO Unit := do
  for (xs, a) in pushArgs do
    line "updates" "pushTwo" "array-u64" [arrU xs, u a, u (a + 1)]
      (words (Examples.Updates.pushTwo xs.toArray a (a + 1)).toList)
    line "updates" "pushCopy" pairKind [arrU xs, u a]
      (pair (Examples.Updates.pushCopy xs.toArray a))
  for (xs, i, j, a) in updateArgs do
    line "updates" "setTwice" "array-u64" [arrU xs, u i, u j, u a]
      (words (Examples.Updates.setTwice xs.toArray i j a).toList)
    line "updates" "insertErase" "array-u64" [arrU xs, u i, u j, u a]
      (words (Examples.Updates.insertErase xs.toArray i j a).toList)

def cases : IO Unit := do
  updatesCases

end Examples.Updates
