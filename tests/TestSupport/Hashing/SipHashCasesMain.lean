module

public import TestSupport.Hashing.SipHashCases

@[expose] public section

/-! The cases of the module `siphash` alone, for `tests/verified/run.sh --cases siphash`. -/

def main : IO Unit := TestSupport.Hashing.SipHashCases.cases
