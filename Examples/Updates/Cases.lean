import Examples.Updates.Program
import Examples.Host

/-! The module cases of `updates`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Updates

open Examples.Host

/-- Chains of updates and a borrowed `push`, at positions inside and past the end of each array. -/
def updatesCases : IO Unit := do
  for xs in wordArrays do
    for i in ([0, 1, 2, 5] : List UInt64) do
      let a := rw (xs.length + i.toNat)
      line "updates" "pushTwo" "array-u64" [arrU xs, u a, u (a + 1)]
        (words (Examples.Updates.pushTwo xs.toArray a (a + 1)).toList)
      line "updates" "pushCopy" pairKind [arrU xs, u a]
        (pair (Examples.Updates.pushCopy xs.toArray a))
      for j in ([0, 1, 3, 7] : List UInt64) do
        line "updates" "setTwice" "array-u64" [arrU xs, u i, u j, u a]
          (words (Examples.Updates.setTwice xs.toArray i j a).toList)
        line "updates" "insertErase" "array-u64" [arrU xs, u i, u j, u a]
          (words (Examples.Updates.insertErase xs.toArray i j a).toList)

def cases : IO Unit := do
  updatesCases

end Examples.Updates
