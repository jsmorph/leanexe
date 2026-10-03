/-!
Binary trees of words declared by the program, held on the heap as records: a leaf is the
null pointer, and `node l k r` a record of three slots, the pointer to `l`, the word `k`, and
the pointer to `r`.  `setKey`, `incr`, `insert`, `dropRight`, and `leftChild` consume their
tree and rewrite its records in place; `insert` allocates one record when the key is new, and
`dropRight` and `leftChild` release the records they drop.
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

/-- The tree with 1 added to every key, modulo 2^64. -/
def KeyTree.incr : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r => .node l.incr (k + 1) r.incr

/-- The search tree `t` with the key `x`: a smaller key goes left, a larger key right, and a
key already present leaves the tree as it is. -/
def KeyTree.insert (x : UInt64) : KeyTree → KeyTree
  | .leaf => .node .leaf x .leaf
  | .node l k r =>
    if x < k then .node (KeyTree.insert x l) k r
    else if k < x then .node l k (KeyTree.insert x r)
    else .node l k r

/-- The tree with the root's right subtree replaced by a leaf. -/
def KeyTree.dropRight : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k _ => .node l k .leaf

/-- The root's left subtree. -/
def KeyTree.leftChild : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l _ _ => l

/-- The tree when `c` is 0, and otherwise a leaf. -/
def KeyTree.keepIf (c : UInt64) (t : KeyTree) : KeyTree := if c = 0 then t else .leaf

/-- The root's left subtree when the root's key is 0, and otherwise the tree with the root's
right subtree replaced by a leaf. -/
def KeyTree.trim : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r => if k = 0 then l else .node l k .leaf

/-- The tree `b` with `a`'s root key added to its root key: `a` is read, `b` rewritten. -/
def KeyTree.addRoot (a : KeyTree) : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r => match a with
    | .leaf => .node l k r
    | .node _ ak _ => .node l (k + ak) r

/-- The tree `b` with `a`'s root key added to every key: `a` is read at every node of `b`, which
is rewritten. -/
def KeyTree.addAll (a : KeyTree) : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r =>
    .node (KeyTree.addAll a l) (k + match a with | .leaf => 0 | .node _ ak _ => ak)
      (KeyTree.addAll a r)

/-- The tree with its left child's root key added to its right child's root key: the left child
is lent to `addRoot`, which rewrites the right child. -/
def KeyTree.addLeft : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r => .node l k (KeyTree.addRoot l r)

/-- The left spine of the second tree, each key increased by the root key of a guide: the first
tree at the root, and below it the right subtree dropped one level up.  Each right subtree is lent
to the recursive call as its guide and then released. -/
def KeyTree.leftSpine (g : KeyTree) : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r =>
    .node (KeyTree.leftSpine r l) (k + match g with | .leaf => 0 | .node _ gk _ => gk) .leaf

/-- The two trees in order when `c` is 0, and swapped otherwise. -/
def KeyTree.pickPair (c : UInt64) (a b : KeyTree) : KeyTree × KeyTree :=
  if c = 0 then (a, b) else (b, a)

/-- The search tree `t` with the keys `a` and then `b`. -/
def KeyTree.insertTwo (a b : UInt64) (t : KeyTree) : KeyTree := (t.insert a).insert b

/-- The number of nodes plus the sum of the keys, modulo 2^64. -/
def KeyTree.sizeSum (t : KeyTree) : UInt64 := t.size + t.sum

/-- `xs` with 1 pushed, and the sum of `t`'s keys: the push writes `xs` in place before `t` is
read. -/
def KeyTree.pushSum (xs : Array UInt64) (t : KeyTree) : Array UInt64 × UInt64 :=
  (xs.push 1, t.sum)

/-- The tree, or a leaf when it has fewer than `n` nodes: `t` is lent to `size`, then released or
returned. -/
def KeyTree.dropSmall (n : UInt64) (t : KeyTree) : KeyTree := if t.size < n then .leaf else t

/-- The number of nodes, and the tree or a leaf when it has fewer than `n` nodes: `t` is lent to
`size` through a word `let`, then released or returned in the pair. -/
def KeyTree.sizeDrop (n : UInt64) (t : KeyTree) : UInt64 × KeyTree :=
  let s := t.size
  if s < n then (s, .leaf) else (s, t)

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
