import TestSupport.PassiveSafety.Cases

/-! The cases of the module `passivesafety` alone, for `tests/verified/run.sh --cases
passivesafety`.  With the argument `--bits`, it prints the lines that
`tests/passivesafety/reference.py` reads, and with `--panels`, the panels that each case's
searches evaluate. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.PassiveSafety.Cases.bits
  else if args == ["--panels"] then TestSupport.PassiveSafety.Cases.panelReport
  else TestSupport.PassiveSafety.Cases.cases
