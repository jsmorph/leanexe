import Examples.Lists.Program
import Project.Compiler.Command

namespace Examples.Lists

open Examples.Lists in
leanexe_compile lists := [listSum, listRange, sumRange]

end Examples.Lists
