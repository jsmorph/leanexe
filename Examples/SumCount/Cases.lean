import Examples.SumCount.Program
import TestSupport.Host

/-! The module cases of `sumCount`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.SumCount

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def samples : List (List UInt64) := wordArrays

def sumCountCases : IO Unit := do
  for xs in samples do
    line "sumCount" "sumCount" "array-u64" [arrU xs]
      (words (Examples.SumCount.sumCount xs.toArray).toList)

def cases : IO Unit := do
  sumCountCases

end Examples.SumCount
