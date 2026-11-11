import TestSupport.Attitude.Cases

/-! The cases of the module `attitude` alone, for `tests/verified/run.sh --cases attitude`.  With
the argument `--bits`, it prints the lines that `tests/attitude/reference.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Attitude.Cases.bits
  else TestSupport.Attitude.Cases.cases
