import TestSupport.Hashing.Sha256Cases

/-! The cases of the module `sha256` alone, for `tests/verified/run.sh --cases sha256`. -/

def main : IO Unit := TestSupport.Hashing.Sha256Cases.cases
