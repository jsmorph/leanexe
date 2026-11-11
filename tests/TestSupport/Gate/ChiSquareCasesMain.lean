import TestSupport.Gate.ChiSquareCases

/-! The cases of the module `chisquare` alone, for `tests/verified/run.sh --cases chisquare`.
With the argument `--bits`, it prints the lines that `tests/gate/distribution.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Gate.ChiSquareCases.bits
  else TestSupport.Gate.ChiSquareCases.cases
