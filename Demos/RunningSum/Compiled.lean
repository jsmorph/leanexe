import Demos.RunningSum.Program
import Verified.Reflect.Command

namespace Demos.RunningSum

open LeanExe.Pipeline

instance : Flat Decimal (Bool × Array UInt64) := ⟨fun value => (value.negative, value.digits)⟩

instance : Flat Parsed (Bool × Decimal) := ⟨fun parsed => (parsed.valid, parsed.value)⟩

verified_compile arithmetic := [zero, parse, magnitudeLess, combineMagnitude, add, render]

end Demos.RunningSum
