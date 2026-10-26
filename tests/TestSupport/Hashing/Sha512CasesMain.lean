import TestSupport.Hashing.Sha512Cases

/-! The cases of the module `sha512` alone, for `tests/verified/run.sh --cases sha512`. -/

def main : IO Unit := TestSupport.Hashing.Sha512Cases.cases
