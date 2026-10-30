import Examples.Updates.Program
import Verified.Reflect.Command

/-! The verified compiler's module of the functions of `Program.lean`, in the order of the
LeanExe compiler's module.  `pushTwo`, `insertErase`, and `pushCopy` take their array as an owned
argument, and `setTwice` borrows it and copies it at the first update.  `compiled.pushTwo.trapFree`
and the others exclude a trap when `top` can rise by the function's bound. -/

namespace Examples.Updates

verified_compile compiled := [pushTwo, setTwice, insertErase, pushCopy]

end Examples.Updates
