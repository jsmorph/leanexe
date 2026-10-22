import Library.Numerics.Statistics.Mean.Program
import TestSupport.Host

/-! The module cases of `mean`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Library.Numerics.Statistics.Mean

open TestSupport.Host

def meanCases : IO Unit := do
  for xs in floatArrays do
    line "mean" "mean" "f64" [arrF xs] (toString (Library.Numerics.Statistics.Mean.mean xs.toArray).toBits)

def cases : IO Unit := do
  meanCases

end Library.Numerics.Statistics.Mean
