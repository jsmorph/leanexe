import Examples.Lists.Program
import LeanExe.Compiler.Command

namespace Examples.Lists

open Examples.Lists in
leanexe_compile lists := [listSum, listRange, sumRange]

end Examples.Lists
