import Examples.Scale.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `scale`.  The function allocates nothing, so the generated
`compiled.scale.implements` states that function 2 computes `scale` without a trap. -/

namespace Examples.Scale

verified_compile compiled := [scale]

end Examples.Scale
