module

public import TestSupport.Bignum.Cases

@[expose] public section

/-! The cases of the module `bignum` alone, for `tests/verified/run.sh --cases bignum`. -/

def main : IO Unit := TestSupport.Bignum.Cases.bignum
