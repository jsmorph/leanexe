import TestSupport.Hashing.Sha3Cases

/-! The cases of the module `sha3` alone, for `tests/verified/run.sh --cases sha3`. -/

def main : IO Unit := TestSupport.Hashing.Sha3Cases.cases
