import LeanExe.Examples.SumArray
import Project.Compiler.Command

namespace Project.SumArray

leanexe_compile sumArray := LeanExe.Examples.SumArray.sumArray

leanexe_compile folds := [LeanExe.Examples.SumArray.productArray,
  LeanExe.Examples.SumArray.xorArray]

end Project.SumArray
