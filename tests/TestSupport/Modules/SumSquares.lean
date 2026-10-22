import Library.Numerics.Statistics.SumSquares.Program
import TestSupport.Host

/-! The module cases of `sumSquares`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Library.Numerics.Statistics.SumSquares

open TestSupport.Host

def sumSquaresCases : IO Unit := do
  for xs in floatArrays do
    line "sumSquares" "sumSquares" "f64" [arrF xs]
      (toString (Library.Numerics.Statistics.SumSquares.sumSquares xs.toArray).toBits)

def cases : IO Unit := do
  sumSquaresCases

end Library.Numerics.Statistics.SumSquares
