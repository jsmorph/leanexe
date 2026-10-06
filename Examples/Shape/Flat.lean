import Examples.Shape.Program
import Project.Pipeline.Implements

/-! How the shape theorems represent `Shape`: the constructor index, then the circle's radius,
then the rectangle's sides, with zeros in the slots of the other constructors.  This instance
is part of what the theorems in `Verify.lean` state. -/

namespace Examples.Shape

open Project.Pipeline Examples.Shape

instance : Flat Shape (UInt64 × Float × UInt64 × UInt64) := ⟨fun
  | .circle r => (0, r, 0, 0)
  | .rect w h => (1, 0, w, h)
  | .point => (2, 0, 0, 0)⟩

example (r : Float) : Scalar.values (Shape.circle r) = [.i64 0, .f64 r.toBits, .i64 0, .i64 0] :=
  rfl

end Examples.Shape
