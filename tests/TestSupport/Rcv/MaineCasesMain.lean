module

public import TestSupport.Rcv.MaineCases

@[expose] public section

/-! The cases of the module `rcvMaine`, for `tests/verified/run.sh --cases rcvMaine`. -/

def main : IO Unit := TestSupport.Rcv.MaineCases.cases
