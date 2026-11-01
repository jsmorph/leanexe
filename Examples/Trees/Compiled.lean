import Examples.Trees.Program
import Library.Trees.WordTree.Reflected
import Verified.Reflect.Command

/-! The verified compiler's module of the operations that `Program.lean` adds over `KeyTree`,
with the library's `size`, `sum`, `incr`, and `insert`, which they call, listed first.  The
functions take or build trees, so their generated `implements` theorems allow a trap at
`unreachable`, and `compiled.f.trapFree` excludes it when `top` can rise by the function's bound
and, for a function whose code takes the call depth, when `compiled.f.fits` holds at depth 1,000. -/

namespace Examples.Trees

verified_compile compiled := [KeyTree.size, KeyTree.sum, KeyTree.incr, KeyTree.insert,
  KeyTree.dropRight, KeyTree.keepIf, KeyTree.trim, KeyTree.addRoot, KeyTree.addAll,
  KeyTree.addLeft, KeyTree.leftSpine, KeyTree.pickPair, KeyTree.keyPair, KeyTree.rootAndRest,
  KeyTree.splitOr, KeyTree.keepOld, KeyTree.addSelf, KeyTree.insertTwo, KeyTree.sizeSum,
  KeyTree.pushSum, KeyTree.dropSmall, KeyTree.sizeDrop, KeyTree.sizeDropNext,
  KeyTree.sizeAfterDrop, KeyTree.sizeDropSmall, KeyTree.sizeFirst, KeyTree.droppedSize,
  KeyTree.dropWithSize, KeyTree.leftSizes, KeyTree.leftHeavy, KeyTree.sumSizes, KeyTree.wide]

end Examples.Trees
