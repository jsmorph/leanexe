import Examples.Calc.Flat
import Verified.Reflect.Command

/-! The verified compiler's module of the functions of `Program.lean`, with the representations
of `Flat.lean`.  The reflector reads the structure patterns of `Calc.undo`, which
fix the field `last` to `.add` and `.sub`, as tests of the word of `last`.  No function
allocates, so each generated `implements` theorem states that its function returns without a
trap. -/

namespace Examples.Calc

verified_compile compiled := [Op.apply, Op.ofWord, Op.inverse, Calc.step, Calc.undo, calcRun]

end Examples.Calc
