import Examples.Lists.Program
import Verified.Reflect.Command

/-! The verified compiler's module of the library's `listSum`, `listRange`, and `sumRange`, in the
order of the LeanExe compiler's module.  The functions take or build lists, so their generated
`implements` theorems allow a trap at `unreachable`, and `compiled.listRange.trapFree` and the
others exclude it when `top` can rise by the function's bound. -/

namespace Examples.Lists

verified_compile compiled := [listSum, listRange, sumRange]

end Examples.Lists
