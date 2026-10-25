import TestSupport.Regex.Cases

/-! The cases of the module `regex` alone, for `tests/verified/run.sh --cases regex`. -/

def main : IO Unit := TestSupport.Regex.Cases.cases
