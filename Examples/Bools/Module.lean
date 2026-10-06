import Examples.Bools.Program
import LeanExe.Compiler.Command

namespace Examples.Bools

open Examples.Bools

leanexe_compile bools := [isPositive, both, either, negate, same, differ, agree, floatSame, inRange,
  pick, anyEqual, mark, flagOf]

end Examples.Bools
