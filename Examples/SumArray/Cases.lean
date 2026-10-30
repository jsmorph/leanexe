import Examples.SumArray.Program
import TestSupport.Host

/-! The module cases of `sumArray and folds`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.SumArray

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def samples : List (List UInt64) := wordArrays

def sumArrayCases : IO Unit := do
  for xs in samples do
    line "sumArray" "sumArray" "i64" [arrU xs] (toString (Library.Numerics.Reductions.Word.sumArray xs.toArray))
    line "folds" "productArray" "i64" [arrU xs]
      (toString (Library.Numerics.Reductions.Word.productArray xs.toArray))
    line "folds" "xorArray" "i64" [arrU xs] (toString (Library.Numerics.Reductions.Word.xorArray xs.toArray))

def cases : IO Unit := do
  sumArrayCases

end Examples.SumArray
