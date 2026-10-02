/-!
Binary trees of words declared by the program, held on the heap as records: a leaf is the
null pointer, and `node l k r` a record of three slots, the pointer to `l`, the word `k`, and
the pointer to `r`.  The functions recurse into both subtrees.
-/

namespace LeanExe.Examples.Trees

/-- A binary tree with a word at each node. -/
inductive Tree where
  | leaf
  | node (left : Tree) (key : UInt64) (right : Tree)

/-- The number of nodes modulo 2^64. -/
def Tree.size : Tree → UInt64
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

end LeanExe.Examples.Trees
