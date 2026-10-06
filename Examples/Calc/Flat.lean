import Examples.Calc.Program
import Project.Pipeline.Implements

/-! How the calculator's theorems represent its types: an operation as the word of its
constructor index, and a state as its value, its step count, and its last operation, in
declaration order.  These instances are part of what the theorems in `Verify.lean` state. -/

namespace Examples.Calc

open Project.Pipeline Examples.Calc

instance : Flat Op UInt64 := ⟨fun op => op.ctorIdx.toUInt64⟩

instance : Flat Calc (UInt64 × UInt64 × Op) := ⟨fun c => (c.value, c.steps, c.last)⟩

example : Scalar.values Op.mul = [.i64 2] := rfl

example : Scalar.values ({ value := 7, steps := 3, last := .sub } : Calc) =
    [.i64 7, .i64 3, .i64 1] := rfl

end Examples.Calc
