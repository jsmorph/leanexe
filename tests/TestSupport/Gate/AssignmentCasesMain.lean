import TestSupport.Gate.AssignmentCases

/-! The cases of the module `assignment` alone, for `tests/verified/run.sh --cases assignment`.
With the argument `--bits`, it prints the lines that `tests/gate/assignment.py` reads. -/

def main (args : List String) : IO Unit :=
  if args == ["--bits"] then TestSupport.Gate.AssignmentCases.bits
  else TestSupport.Gate.AssignmentCases.cases
