import TestSupport.Slew.Cases

/-! The cases of the module `slew` alone, for `tests/verified/run.sh --cases slew`.  With the
argument `--summary`, it prints the count of each class's statuses and the least spare of the
sampled safety check instead of the cases. -/

def main (args : List String) : IO Unit :=
  TestSupport.Slew.Cases.run (args == ["--summary"])
