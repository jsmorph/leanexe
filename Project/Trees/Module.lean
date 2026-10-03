import LeanExe.Examples.Trees
import Project.Compiler.Command

namespace Project.Trees

open LeanExe.Examples.Trees in
leanexe_compile trees := [KeyTree.size, KeyTree.sum, KeyTree.height, KeyTree.sizeSum,
  KeyTree.pushSum, KeyTree.dropSmall,
  KeyTree.sizeDrop, KeyTree.sizeDropNext, KeyTree.sizeAfterDrop, KeyTree.sizeDropSmall,
  KeyTree.sizeFirst, KeyTree.droppedSize, KeyTree.dropWithSize]

end Project.Trees
