module

public import TestSupport.Hashing.CrcBitwiseCases

@[expose] public section

/-! The cases of the module `crcBitwise` alone, for `tests/verified/run.sh --cases crcBitwise`. -/

def main : IO Unit := TestSupport.Hashing.CrcBitwiseCases.cases
