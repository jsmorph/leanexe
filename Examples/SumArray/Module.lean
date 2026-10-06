import Examples.SumArray.Program
import LeanExe.Compiler.Command

namespace Examples.SumArray

leanexe_compile sumArray := Examples.SumArray.sumArray

leanexe_compile folds := [Examples.SumArray.productArray,
  Examples.SumArray.xorArray]

end Examples.SumArray
