import Examples.Bools.Program
import LeanExe.Pipeline.Implements

/-! How the theorems of both compilers represent `Flagged`: its flag and its value, in declaration
order.  The instance is part of what the theorems in `Verify.lean` and `Compiled.lean` state. -/

namespace Examples.Bools

open LeanExe.Pipeline

instance : Flat Flagged (Bool × UInt64) := ⟨fun f => (f.flag, f.value)⟩

end Examples.Bools
