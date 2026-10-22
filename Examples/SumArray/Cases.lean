import Examples.SumArray.Program
import TestSupport.Host

/-! The module cases of `sumArray and folds`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.SumArray

open TestSupport.Host

def sumArrayCases : IO Unit := do
  for xs in wordArrays do
    line "sumArray" "sumArray" "i64" [arrU xs] (toString (Examples.SumArray.sumArray xs.toArray))
    line "folds" "productArray" "i64" [arrU xs]
      (toString (Examples.SumArray.productArray xs.toArray))
    line "folds" "xorArray" "i64" [arrU xs] (toString (Examples.SumArray.xorArray xs.toArray))

def cases : IO Unit := do
  sumArrayCases

end Examples.SumArray
