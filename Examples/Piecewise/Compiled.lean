module

public import Examples.Piecewise.Program
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compiler's module of `piecewise`.  The function allocates nothing, so the generated
`compiled.piecewise.implements` states that function 2 computes `piecewise` without a trap. -/

namespace Examples.Piecewise

verified_compile compiled := [piecewise]

end Examples.Piecewise
