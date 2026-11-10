import TestSupport.Conjunction.Cases

/-! The cases of the module `conjunction` alone, for `tests/verified/run.sh --cases conjunction`.
With the argument `--bits`, it prints the lines that `tests/conjunction/reference.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Conjunction.Cases.bits
  else TestSupport.Conjunction.Cases.cases
