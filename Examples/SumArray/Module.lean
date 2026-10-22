import Examples.SumArray.Program
import LeanExe.Compiler.Command

namespace Examples.SumArray

leanexe_compile sumArray := Library.Numerics.Reductions.Word.sumArray

leanexe_compile folds := [Library.Numerics.Reductions.Word.productArray,
  Library.Numerics.Reductions.Word.xorArray]

end Examples.SumArray
