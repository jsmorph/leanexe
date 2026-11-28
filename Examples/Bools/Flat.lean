module

public import Examples.Bools.Program
public import LeanExe.Pipeline.Implements

@[expose] public section

/-! How the theorems represent `Flagged`: its flag and its value, in declaration order.  The
instance is part of what the theorems of `Compiled.lean` state. -/

namespace Examples.Bools

open LeanExe.Pipeline

instance : Flat Flagged (Bool × UInt64) := ⟨fun f => (f.flag, f.value)⟩

end Examples.Bools
