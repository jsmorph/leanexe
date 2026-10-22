import Examples.RemoveZero.Program
import LeanExe.Compiler.Command

namespace Examples.RemoveZero

open Examples.RemoveZero

leanexe_compile removeZero := [Library.Arrays.Search.firstZero, compute]

end Examples.RemoveZero
