import Examples.Axpy.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `axpy`.  The function allocates nothing, so the generated
`compiled.axpy.implements` states that function 2 computes `axpy` without a trap. -/

namespace Examples.Axpy

verified_compile compiled := [axpy]

end Examples.Axpy
