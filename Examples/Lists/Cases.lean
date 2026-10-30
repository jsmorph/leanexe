import Examples.Lists.Program
import TestSupport.Host

/-! The module cases of `lists`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Lists

open TestSupport.Host

/-- The lists of the cases of `listSum`, which the verified compiler's cases also use. -/
def listArgs : List (List UInt64) :=
  let chosen : List (List UInt64) :=
    [[], [0], [maxU], [maxU, 1], [1, 2, 3], [maxU, maxU, maxU], (List.range 200).map rw]
  let random := (List.range 30).map fun i => (List.range (i % 13)).map fun k => rw (13 * i + k)
  chosen ++ random

/-- The counts of the cases of `listRange` and `sumRange`, which the verified compiler's cases
also use. -/
def rangeArgs : List UInt64 := [0, 1, 2, 3, 7, 64, 65, 300, 1000]

def listCases : IO Unit := do
  for xs in listArgs do
    line "lists" "listSum" "i64" [chain xs] (toString (Library.Lists.Word.listSum xs))
  for n in rangeArgs do
    line "lists" "listRange" "chain-u64" [u n] (words (Examples.Lists.listRange n))
    line "lists" "sumRange" "i64" [u n] (toString (Examples.Lists.sumRange n))

def cases : IO Unit := do
  listCases

end Examples.Lists
