import TestSupport.Geolocation.Cases

/-! The cases of the module `geolocation` alone, for `tests/verified/run.sh --cases geolocation`. -/

def main : IO Unit := TestSupport.Geolocation.Cases.cases
