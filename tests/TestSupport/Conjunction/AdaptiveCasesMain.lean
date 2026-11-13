import TestSupport.Conjunction.AdaptiveCases
import TestSupport.Conjunction.Evaluate

/-! The cases of the module `adaptive` alone, for `tests/verified/run.sh --cases adaptive`.  With
the argument `--bits` or `--sweep`, it prints the lines that `tests/conjunction/accuracy.py`
reads, and with `--evaluate FILE` the results on the inputs of `FILE` that
`tests/conjunction/benchmark.py` reads. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--bits"] => TestSupport.Conjunction.AdaptiveCases.bits
  | ["--sweep"] => TestSupport.Conjunction.AdaptiveCases.sweep
  | ["--evaluate", file] => return ← TestSupport.Conjunction.Evaluate.run file
  | _ => TestSupport.Conjunction.AdaptiveCases.cases
  return 0
