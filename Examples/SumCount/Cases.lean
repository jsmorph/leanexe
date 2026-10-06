import Examples.SumCount.Program
import Examples.Host

/-! The module cases of `sumCount`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.SumCount

open Examples.Host

def sumCountCases : IO Unit := do
  for xs in wordArrays do
    line "sumCount" "sumCount" "array-u64" [arrU xs]
      (words (Examples.SumCount.sumCount xs.toArray).toList)

def cases : IO Unit := do
  sumCountCases

end Examples.SumCount
