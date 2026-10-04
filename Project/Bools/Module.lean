import LeanExe.Examples.Bools
import Project.Compiler.Command

namespace Project.Bools

open LeanExe.Examples.Bools

leanexe_compile bools := [isPositive, both, either, negate, same, differ, agree, floatSame, inRange,
  pick, anyEqual, mark, flagOf]

end Project.Bools
