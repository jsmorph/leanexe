import Examples.SumCount.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `sumCount`, whose result is the two-word literal
`#[sum, size]`, which the reflector reads as two pushes onto `#[]`.  `compiled.sumCount.trapFree`
excludes a trap when `top` can rise by the bound of the empty block and the two pushes. -/

namespace Examples.SumCount

verified_compile compiled := [sumCount]

end Examples.SumCount
