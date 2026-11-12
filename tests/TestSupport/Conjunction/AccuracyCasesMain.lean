import TestSupport.Conjunction.AccuracyCases

/-! The cases of the module `accuracy` alone, for `tests/verified/run.sh --cases accuracy`.  With
the argument `--bits`, it prints the lines that `tests/conjunction/accuracy.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Conjunction.AccuracyCases.bits
  else TestSupport.Conjunction.AccuracyCases.cases
