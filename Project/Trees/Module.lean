import LeanExe.Examples.Trees
import Project.Compiler.Command

namespace Project.Trees

open LeanExe.Examples.Trees in
leanexe_compile trees := [KeyTree.size, KeyTree.sum, KeyTree.height, KeyTree.sizeSum]

end Project.Trees
