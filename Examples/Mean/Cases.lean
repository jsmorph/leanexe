import Examples.Mean.Program
import Examples.Host

/-! The module cases of `mean`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Mean

open Examples.Host

def meanCases : IO Unit := do
  for xs in floatArrays do
    line "mean" "mean" "f64" [arrF xs] (toString (Examples.Mean.mean xs.toArray).toBits)

def cases : IO Unit := do
  meanCases

end Examples.Mean
