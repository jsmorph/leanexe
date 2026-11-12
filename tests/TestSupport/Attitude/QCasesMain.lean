import TestSupport.Attitude.QCases

/-! The cases of the module `qmethod` alone, for `tests/verified/run.sh --cases qmethod`.  With
the argument `--bits`, it prints the lines that `tests/attitude/qreference.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Attitude.QCases.bits
  else TestSupport.Attitude.QCases.cases
