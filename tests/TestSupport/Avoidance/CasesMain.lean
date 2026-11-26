module

public import TestSupport.Avoidance.Cases

@[expose] public section

/-! The cases of the module `avoidance` alone, for `tests/verified/run.sh --cases avoidance`. -/

def main : IO Unit := TestSupport.Avoidance.Cases.cases
