import Examples.Trees.Program
import LeanExe.Compiler.Command

namespace Examples.Trees

open Examples.Trees in
leanexe_compile trees := [KeyTree.size, KeyTree.sum, KeyTree.height, KeyTree.sizeSum,
  KeyTree.pushSum, KeyTree.dropSmall,
  KeyTree.sizeDrop, KeyTree.sizeDropNext, KeyTree.sizeAfterDrop, KeyTree.sizeDropSmall,
  KeyTree.sizeFirst, KeyTree.droppedSize, KeyTree.dropWithSize, KeyTree.leftSizes,
  KeyTree.leftHeavy, KeyTree.sumSizes, KeyTree.keyPair]

end Examples.Trees
