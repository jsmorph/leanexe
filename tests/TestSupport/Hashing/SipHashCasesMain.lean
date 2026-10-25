import TestSupport.Hashing.SipHashCases

/-! The cases of the module `siphash` alone, for `tests/verified/run.sh --cases siphash`. -/

def main : IO Unit := TestSupport.Hashing.SipHashCases.cases
