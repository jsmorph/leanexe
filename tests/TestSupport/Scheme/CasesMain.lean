module

public import TestSupport.Scheme.Cases

@[expose] public section

/-! The cases of the module `scheme`, for `tests/verified/run.sh --cases scheme`.  The executable
fails when a native result differs from the reference semantics's. -/

def main : IO UInt32 := do
  let failures ← TestSupport.Scheme.Cases.cases
  return if failures == 0 then 0 else 1
