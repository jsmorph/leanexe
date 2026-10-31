import TestSupport.Modules.Gcd
import TestSupport.Modules.SumSquares
import TestSupport.Modules.Mean
import Demos.Clob.Cases
import Examples.Shape.Cases
import Demos.Euler.Cases
import Demos.Drone.Cases
import TestSupport.Modules.PrimeFactors

/-! Test cases computed by native Lean for the LeanExe library and demo modules other than
`gpt.wasm` and `prng.wasm`, and for `shapes`, whose cases `tests/verified/run.sh` runs on the
verified `sums` module.  Each `Cases.lean` prints its cases, one line per case:
`module|export|result kind|host arguments|expected result`, with floats given as bit
patterns and a pair of arrays as the two arrays' words joined by a comma.
`tests/modules/run.sh` passes the arguments to the Wasmtime host running
`build/MODULE/MODULE.wasm`, or the module that `--module` names, and compares its output.  Run
with `lake env lean --run`. -/

def main : IO Unit := do
  Library.Numerics.Arithmetic.Gcd.cases
  Library.Numerics.Statistics.SumSquares.cases
  Library.Numerics.Statistics.Mean.cases
  Demos.Clob.cases
  Examples.Shape.cases
  Demos.Euler.cases
  Demos.Drone.cases
  Library.Numerics.Arithmetic.PrimeFactors.cases
