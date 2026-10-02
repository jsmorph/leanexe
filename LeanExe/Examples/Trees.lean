/-!
Binary trees of words declared by the program, held on the heap as records: a leaf is the
null pointer, and `node l k r` a record of three slots, the pointer to `l`, the word `k`, and
the pointer to `r`.  The functions recurse into both subtrees, except `setKey`, which consumes
its tree and rewrites the root's record.
-/

namespace LeanExe.Examples.Trees

/-- A binary tree with a word at each node. -/
inductive KeyTree where
  | leaf
  | node (left : KeyTree) (key : UInt64) (right : KeyTree)

/-- The number of nodes modulo 2^64. -/
def KeyTree.size : KeyTree → UInt64
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

/-- The sum of the keys modulo 2^64. -/
def KeyTree.sum : KeyTree → UInt64
  | .leaf => 0
  | .node l k r => l.sum + k + r.sum

/-- The number of nodes on the longest path from the root. -/
def KeyTree.height : KeyTree → UInt64
  | .leaf => 0
  | .node l _ r => max l.height r.height + 1

/-- The tree with the root's key replaced by `k`. -/
def KeyTree.setKey (k : UInt64) : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l _ r => .node l k r

/-- A test of the depth limit: sixteen words computed before the recursive calls and used after
them, so that the internal function holds 24 values in its frame, the most the compiler
accepts, and keeps them live across its calls. -/
def KeyTree.wide : KeyTree → UInt64
  | .leaf => 0
  | .node l k r =>
    let a1 := k + 1
    let a2 := k + 2
    let a3 := k + 3
    let a4 := k + 4
    let a5 := k + 5
    let a6 := k + 6
    let a7 := k + 7
    let a8 := k + 8
    let a9 := k + 9
    let a10 := k + 10
    let a11 := k + 11
    let a12 := k + 12
    let a13 := k + 13
    let a14 := k + 14
    let a15 := k + 15
    let a16 := k + 16
    l.wide + r.wide + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16

end LeanExe.Examples.Trees
