import Examples.SumSquares.Program
import Examples.Host

/-! The module cases of `sumSquares`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.SumSquares

open Examples.Host

def sumSquaresCases : IO Unit := do
  for xs in floatArrays do
    line "sumSquares" "sumSquares" "f64" [arrF xs]
      (toString (Examples.SumSquares.sumSquares xs.toArray).toBits)

def cases : IO Unit := do
  sumSquaresCases

end Examples.SumSquares
