module

public import TestSupport.Screening.Cases

@[expose] public section

/-! The cases of the module `screening` alone, for `tests/verified/run.sh --cases screening`. -/

def main : IO Unit := TestSupport.Screening.Cases.cases
