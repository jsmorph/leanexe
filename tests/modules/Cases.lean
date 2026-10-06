import Examples.Scale.Cases
import Examples.Gcd.Cases
import Examples.SumArray.Cases
import Examples.PairSum.Cases
import Examples.SumCount.Cases
import Examples.Axpy.Cases
import Examples.ScaledHypot.Cases
import Examples.Binary32.Cases
import Examples.Piecewise.Cases
import Examples.SumSquares.Cases
import Examples.Mean.Cases
import Examples.Bucket.Cases
import Examples.Clob.Cases
import Examples.Calc.Cases
import Examples.Shape.Cases
import Examples.Lists.Cases
import Examples.Words.Cases
import Examples.Trees.Cases
import Examples.Updates.Cases
import Examples.Bools.Cases
import Examples.Grids.Cases
import Examples.Euler.Cases
import Examples.Drone.Cases
import Examples.Increment.Cases
import Examples.RemoveZero.Cases
import Examples.PrimeFactors.Cases
import Examples.Lookup.Cases
import Examples.Below100.Cases
import Examples.TreeLookup.Cases

/-! Test cases for the modules other than `gpt.wasm` and `prng.wasm`, computed by native
Lean.  Each example's `Cases.lean` prints its cases, one line per case:
`module|export|result kind|host arguments|expected result`, with floats given as bit
patterns and a pair of arrays as the two arrays' words joined by a comma.
`tests/modules/run.sh` passes the arguments to the Wasmtime host running
`build/MODULE/MODULE.wasm` and compares its output.  Run with `lake env lean --run`. -/

def main : IO Unit := do
  Examples.Scale.cases
  Examples.Gcd.cases
  Examples.SumArray.cases
  Examples.PairSum.cases
  Examples.SumCount.cases
  Examples.Axpy.cases
  Examples.ScaledHypot.cases
  Examples.Binary32.cases
  Examples.Piecewise.cases
  Examples.SumSquares.cases
  Examples.Mean.cases
  Examples.Bucket.cases
  Examples.Clob.cases
  Examples.Calc.cases
  Examples.Shape.cases
  Examples.Lists.cases
  Examples.Words.cases
  Examples.Trees.cases
  Examples.Updates.cases
  Examples.Bools.cases
  Examples.Grids.cases
  Examples.Euler.cases
  Examples.Drone.cases
  Examples.Increment.cases
  Examples.RemoveZero.cases
  Examples.PrimeFactors.cases
  Examples.Lookup.cases
  Examples.Below100.cases
  Examples.TreeLookup.cases
