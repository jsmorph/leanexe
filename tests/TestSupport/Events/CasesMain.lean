module

public import TestSupport.Events.Cases

@[expose] public section

/-! The cases of the module `events` alone, for `tests/verified/run.sh --cases events`. -/

def main : IO Unit := TestSupport.Events.Cases.cases
