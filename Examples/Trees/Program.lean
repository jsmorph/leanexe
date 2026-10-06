import LeanExe.Dialect.Loop

/-!
Binary trees of words declared by the program, held on the heap as records: a leaf is the
null pointer, and `node l k r` a record of three slots, the pointer to `l`, the word `k`, and
the pointer to `r`.  `setKey`, `incr`, `insert`, `dropRight`, and `leftChild` consume their
tree and rewrite its records in place; `insert` allocates one record when the key is new, and
`dropRight` and `leftChild` release the records they drop.
-/

namespace Examples.Trees

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

/-- The root key and the root key plus one, or two zeros for a leaf: a pair-valued match that
reads the tree. -/
def KeyTree.keyPair (t : KeyTree) : UInt64 × UInt64 := match t with
  | .leaf => (0, 0)
  | .node _ k _ => (k, k + 1)

/-- The two subtrees: the record branch moves both children into the pair and releases the root
record. -/
def KeyTree.splitRoot (t : KeyTree) : KeyTree × KeyTree := match t with
  | .leaf => (.leaf, .leaf)
  | .node l _ r => (l, r)

/-- The root key, and the tree with its root key set to 0: the record branch rewrites the record
in place. -/
def KeyTree.rootAndRest (t : KeyTree) : UInt64 × KeyTree := match t with
  | .leaf => (0, .leaf)
  | .node l k r => (k, .node l 0 r)

/-- `a`'s subtrees when `a` is a node, and `b` with a leaf otherwise: the record branch releases
`b`, which only the other branch moves. -/
def KeyTree.splitOr (a b : KeyTree) : KeyTree × KeyTree := match a with
  | .leaf => (b, .leaf)
  | .node l _ r => (l, r)

/-- The tree with 1 added to every key, and the tree: `incr` consumes a copy of `t`, and the pair
holds `t` itself. -/
def KeyTree.keepOld (t : KeyTree) : KeyTree × KeyTree := (t.incr, t)

/-- The tree with its root key doubled: `addRoot` reads `t` and rewrites a copy of it. -/
def KeyTree.addSelf (t : KeyTree) : KeyTree := KeyTree.addRoot t t

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

/-- `sizeDrop`'s size plus one, and its tree: the caller passes the tree component through. -/
def KeyTree.sizeDropNext (n : UInt64) (t : KeyTree) : UInt64 × KeyTree :=
  match t.sizeDrop n with | (s, u) => (s + 1, u)

/-- `sizeDrop`'s size: the caller drops the tree component, which it releases at the end. -/
def KeyTree.sizeAfterDrop (n : UInt64) (t : KeyTree) : UInt64 :=
  match t.sizeDrop n with | (s, _) => s

/-- `sizeDrop`'s tree, or a leaf when it has fewer than its size plus one nodes: the caller passes
the tree component to `dropSmall`, which consumes it. -/
def KeyTree.sizeDropSmall (n : UInt64) (t : KeyTree) : KeyTree :=
  match t.sizeDrop n with | (s, u) => u.dropSmall (s + 1)

/-- `sizeDrop`'s size, by projection: the tree component is released right after the call. -/
def KeyTree.sizeFirst (n : UInt64) (t : KeyTree) : UInt64 := (t.sizeDrop n).1

/-- The size of `dropSmall`'s result: the `let` binds the result, lends it to `size`, and
releases it at the end. -/
def KeyTree.droppedSize (n : UInt64) (t : KeyTree) : UInt64 :=
  let u := t.dropSmall n
  u.size

/-- `dropSmall`'s result with its size: the `let` binds the result, lends it to `size`, and
returns it. -/
def KeyTree.dropWithSize (n : UInt64) (t : KeyTree) : UInt64 × KeyTree :=
  let u := t.dropSmall n
  (u.size, u)

/-- The tree with each node's key replaced by the size of its left subtree: each record branch
lends its left child to `size`. -/
def KeyTree.leftSizes : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l _ r =>
    let n := l.size
    .node (KeyTree.leftSizes l) n (KeyTree.leftSizes r)

/-- The number of nodes whose left subtree has more nodes than their right one. -/
def KeyTree.leftHeavy : KeyTree → UInt64
  | .leaf => 0
  | .node l _ r =>
    (if r.size < l.size then 1 else 0) + KeyTree.leftHeavy l + KeyTree.leftHeavy r

/-- `t`'s size added `n` times: the loop body lends `t` to `size`. -/
def KeyTree.sumSizes (n : UInt64) (t : KeyTree) : UInt64 :=
  LeanExe.loop n 0 fun _ acc => acc + t.size

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

end Examples.Trees
