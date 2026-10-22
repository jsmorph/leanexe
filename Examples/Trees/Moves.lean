import Examples.Trees.Program
import LeanExe.Compiler.Command

/-! The functions over `KeyTree` that consume their tree. -/

namespace Examples.Trees

open Examples.Trees in
leanexe_compile treeMoves := [Library.Trees.WordTree.KeyTree.setKey, Library.Trees.WordTree.KeyTree.incr, Library.Trees.WordTree.KeyTree.insert, KeyTree.dropRight,
  Library.Trees.WordTree.KeyTree.leftChild, KeyTree.keepIf, KeyTree.trim, KeyTree.insertTwo, KeyTree.addRoot,
  KeyTree.addAll, KeyTree.addLeft, KeyTree.leftSpine,
  KeyTree.pickPair, Library.Trees.WordTree.KeyTree.splitRoot, KeyTree.rootAndRest, KeyTree.splitOr,
  KeyTree.keepOld, KeyTree.addSelf]

end Examples.Trees
