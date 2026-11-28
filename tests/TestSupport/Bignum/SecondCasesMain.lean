module

public import TestSupport.Bignum.Cases

@[expose] public section

/-! The cases of the module `bignum2` alone, for `tests/verified/run.sh --cases bignum2`. -/

def main : IO Unit := TestSupport.Bignum.Cases.bignum2
