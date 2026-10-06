import Examples.Trees.Program
import LeanExe.Compiler.Command

/-! A module for the depth test only, without theorems: `KeyTree.wide`'s internal function
holds 24 values in its frame, the most the compiler accepts. -/

namespace Examples.Trees

open Examples.Trees in
leanexe_compile treeFrame := [KeyTree.wide]

end Examples.Trees
