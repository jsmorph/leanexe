import Examples.Calc.Program
import Project.Compiler.Command

namespace Examples.Calc

open Examples.Calc in
leanexe_compile calculator := [Op.apply, Op.ofWord, Op.inverse, Calc.step, Calc.undo, calcRun]

end Examples.Calc
