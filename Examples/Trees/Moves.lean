import Examples.Trees.Program
import LeanExe.Compiler.Command

/-! The functions over `KeyTree` that consume their tree. -/

namespace Examples.Trees

open Examples.Trees in
leanexe_compile treeMoves := [KeyTree.setKey, KeyTree.incr, KeyTree.insert, KeyTree.dropRight,
  KeyTree.leftChild, KeyTree.keepIf, KeyTree.trim, KeyTree.insertTwo, KeyTree.addRoot,
  KeyTree.addAll, KeyTree.addLeft, KeyTree.leftSpine,
  KeyTree.pickPair, KeyTree.splitRoot, KeyTree.rootAndRest, KeyTree.splitOr,
  KeyTree.keepOld, KeyTree.addSelf]

end Examples.Trees
