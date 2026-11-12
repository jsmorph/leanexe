import TestSupport.Conjunction.AdaptiveCases

/-! The cases of the module `adaptive` alone, for `tests/verified/run.sh --cases adaptive`.  With
the argument `--bits` or `--sweep`, it prints the lines that `tests/conjunction/accuracy.py`
reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Conjunction.AdaptiveCases.bits
  else if args == ["--sweep"] then TestSupport.Conjunction.AdaptiveCases.sweep
  else TestSupport.Conjunction.AdaptiveCases.cases
