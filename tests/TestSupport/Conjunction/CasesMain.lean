import TestSupport.Conjunction.Cases

/-! The cases of the module `conjunction` alone, for `tests/verified/run.sh --cases conjunction`.
With the argument `--bits`, it prints the lines that `tests/conjunction/reference.py` reads, and
with `--message` those that `tests/conjunction/message.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Conjunction.Cases.bits
  else if args == ["--message"] then TestSupport.Conjunction.Cases.messageBits
  else TestSupport.Conjunction.Cases.cases
