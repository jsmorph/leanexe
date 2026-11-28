module

public import TestSupport.Rcv.Cases

@[expose] public section

/-! The cases of the modules `rcvCount` and `rcvTabulate`, for `tests/verified/run.sh --cases` with
either name. -/

def main : IO Unit := TestSupport.Rcv.Cases.cases
