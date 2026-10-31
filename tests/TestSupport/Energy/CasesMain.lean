import TestSupport.Energy.Cases

/-! The cases of the module `energy` alone, for `tests/verified/run.sh --cases energy`.  With the
argument `--summary`, it prints the count of each class's statuses instead of the cases. -/

def main (args : List String) : IO Unit :=
  TestSupport.Energy.Cases.run (args == ["--summary"])
