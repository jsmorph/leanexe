import Examples.PairSum.Program
import TestSupport.Host

/-! The module cases of `pairSum`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.PairSum

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def samples : List (UInt64 × UInt64) :=
  let chosen : List (UInt64 × UInt64) := [(3, 4), (maxU, 2), (0, 0), (maxU, maxU)]
  let random := (List.range 30).map fun i => (rw (2 * i + 300), rw (2 * i + 301))
  chosen ++ random

def pairSumCases : IO Unit := do
  for (a, b) in samples do
    line "pairSum" "pairSum" "i64" [u a, u b] (toString (Examples.PairSum.pairSum a b))

def cases : IO Unit := do
  pairSumCases

end Examples.PairSum
