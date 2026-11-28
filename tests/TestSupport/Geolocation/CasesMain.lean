module

public import TestSupport.Geolocation.Cases

@[expose] public section

/-! The cases of the module `geolocation` alone, for `tests/verified/run.sh --cases geolocation`. -/

def main : IO Unit := TestSupport.Geolocation.Cases.cases
