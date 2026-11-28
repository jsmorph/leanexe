module

public import TestSupport.BignumCalc.Cases

@[expose] public section

/-! The cases of the module `bignumCalc` alone, for `tests/verified/run.sh --cases bignumCalc`. -/

def main : IO Unit := TestSupport.BignumCalc.Cases.bignumCalc
