import LeanExe.Examples.Trees
import Project.Compiler.Command

namespace Project.Trees

open LeanExe.Examples.Trees in
leanexe_compile trees := [Tree.size]

end Project.Trees
