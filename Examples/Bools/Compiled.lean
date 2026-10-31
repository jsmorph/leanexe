import Examples.Bools.Flat
import Verified.Reflect.Command

/-! The verified compiler's module of the functions of `Program.lean`.  `Flagged` has the
representation of `Flat.lean`.  No function allocates, so each generated `implements`
theorem states that its function returns without a trap. -/

namespace Examples.Bools

verified_compile compiled := [isPositive, both, either, negate, same, differ, agree, floatSame,
  inRange, pick, anyEqual, mark, flagOf]

end Examples.Bools
