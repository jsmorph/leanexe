module

public import TestSupport.Hashing.Sha3Cases

@[expose] public section

/-! The cases of the module `sha3` alone, for `tests/verified/run.sh --cases sha3`. -/

def main : IO Unit := TestSupport.Hashing.Sha3Cases.cases
