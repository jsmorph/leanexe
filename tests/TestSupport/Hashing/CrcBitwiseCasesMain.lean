import TestSupport.Hashing.CrcBitwiseCases

/-! The cases of the module `crcBitwise` alone, for `tests/verified/run.sh --cases crcBitwise`. -/

def main : IO Unit := TestSupport.Hashing.CrcBitwiseCases.cases
