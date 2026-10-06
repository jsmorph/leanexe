import Examples.Lists.Program
import Examples.Host

/-! The module cases of `lists`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Lists

open Examples.Host

def listCases : IO Unit := do
  let chosen : List (List UInt64) :=
    [[], [0], [maxU], [maxU, 1], [1, 2, 3], [maxU, maxU, maxU], (List.range 200).map rw]
  let random := (List.range 30).map fun i => (List.range (i % 13)).map fun k => rw (13 * i + k)
  for xs in chosen ++ random do
    line "lists" "listSum" "i64" [chain xs] (toString (Examples.Lists.listSum xs))
  for n in [0, 1, 2, 3, 7, 64, 65, 300, 1000] do
    line "lists" "listRange" "chain-u64" [u n] (words (Examples.Lists.listRange n))
    line "lists" "sumRange" "i64" [u n] (toString (Examples.Lists.sumRange n))

def cases : IO Unit := do
  listCases

end Examples.Lists
