import TestSupport.Sgp4.OmmCases

/-! The cases of the module `sgp4omm` alone, for `tests/verified/run.sh --cases sgp4omm`. -/

def main : IO Unit := TestSupport.Sgp4.OmmCases.cases
