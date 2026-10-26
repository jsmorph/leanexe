import TestSupport.Hashing.XxHash64Cases

/-! The cases of the module `xxhash64` alone, for `tests/verified/run.sh --cases xxhash64`. -/

def main : IO Unit := TestSupport.Hashing.XxHash64Cases.cases
