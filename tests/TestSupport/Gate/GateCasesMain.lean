import TestSupport.Gate.GateCases

/-! The cases of the module `gate` alone, for `tests/verified/run.sh --cases gate`.  With the
argument `--bits`, it prints the lines that `tests/gate/gate.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Gate.GateCases.bits
  else TestSupport.Gate.GateCases.cases
