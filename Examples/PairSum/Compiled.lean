module

public import Examples.PairSum.Program
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compiler's module of `pairSum`.  The reflector reads the literal `#[a, b]` as two
pushes onto `#[]`, and `compiled.pairSum.trapFree` excludes a trap when `top` can rise by the bound
of the empty block and the two pushes. -/

namespace Examples.PairSum

verified_compile compiled := [pairSum]

end Examples.PairSum
