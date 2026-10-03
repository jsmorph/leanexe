import LeanExe.Examples.Trees
import Project.Compiler.Command

/-! The functions over `KeyTree` that consume their tree. -/

namespace Project.Trees

open LeanExe.Examples.Trees in
leanexe_compile treeMoves := [KeyTree.setKey, KeyTree.incr, KeyTree.insert, KeyTree.dropRight,
  KeyTree.leftChild, KeyTree.keepIf, KeyTree.trim, KeyTree.insertTwo, KeyTree.addRoot,
  KeyTree.addAll]

end Project.Trees
