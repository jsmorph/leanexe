import TestSupport.Hashing.CrcCases

/-! The cases of the module `crc` alone, for `tests/verified/run.sh --cases crc`. -/

def main : IO Unit := TestSupport.Hashing.CrcCases.cases
