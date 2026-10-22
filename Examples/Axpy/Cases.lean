import Examples.Axpy.Program
import TestSupport.Host

/-! The module cases of `axpy`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Axpy

open TestSupport.Host

def axpyCases : IO Unit := do
  for (a, x, y) in floatTriples do
    line "axpy" "axpy" "f64" [fl a, fl x, fl y] (toString (Examples.Axpy.axpy a x y).toBits)

def cases : IO Unit := do
  axpyCases

end Examples.Axpy
