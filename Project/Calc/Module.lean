import LeanExe.Examples.Calc
import Project.Compiler.Command

namespace Project.Calc

open LeanExe.Examples.Calc in
leanexe_compile calculator := [Op.apply, Op.ofWord, Op.inverse, Calc.step, Calc.undo, calcRun]

end Project.Calc
