import TestSupport.Modules.Gcd
import TestSupport.Modules.SumSquares
import TestSupport.Modules.Mean
import Examples.Shape.Cases
import Demos.Euler.Cases
import TestSupport.Modules.PrimeFactors

/-! Test cases computed by native Lean for the LeanExe library modules other than `prng.wasm`, and
for `euler` and `shapes`, whose cases `tests/verified/run.sh` runs on the verified `euler` and
`sums` modules.  Each `Cases.lean` prints its cases, one line per case:
`module|export|result kind|host arguments|expected result`, with floats given as bit
patterns and a pair of arrays as the two arrays' words joined by a comma.
`tests/modules/run.sh` passes the arguments to the Wasmtime host running
`build/MODULE/MODULE.wasm`, or the module that `--module` names, and compares its output.  Run
with `lake env lean --run`. -/

def main : IO Unit := do
  Library.Numerics.Arithmetic.Gcd.cases
  Library.Numerics.Statistics.SumSquares.cases
  Library.Numerics.Statistics.Mean.cases
  Examples.Shape.cases
  Demos.Euler.cases
  Library.Numerics.Arithmetic.PrimeFactors.cases
