module

public import TestSupport.Bignum.Cases

@[expose] public section

/-! The cases of the module `bignum3` alone, for `tests/verified/run.sh --cases bignum3`. -/

def main : IO Unit := TestSupport.Bignum.Cases.bignum3
