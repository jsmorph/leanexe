namespace Library.Trees.WordTree

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

/-- The tree with 1 added to every key, modulo 2^64. -/
def KeyTree.incr : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r => .node l.incr (k + 1) r.incr

/-- The tree with the root's key replaced by `k`. -/
def KeyTree.setKey (k : UInt64) : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l _ r => .node l k r

/-- The search tree `t` with the key `x`: a smaller key goes left, a larger key right, and a
key already present leaves the tree as it is. -/
def KeyTree.insert (x : UInt64) : KeyTree → KeyTree
  | .leaf => .node .leaf x .leaf
  | .node l k r =>
    if x < k then .node (KeyTree.insert x l) k r
    else if k < x then .node l k (KeyTree.insert x r)
    else .node l k r

/-- The root's left subtree. -/
def KeyTree.leftChild : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l _ _ => l

/-- The two subtrees: the record branch moves both children into the pair and releases the root
record. -/
def KeyTree.splitRoot (t : KeyTree) : KeyTree × KeyTree := match t with
  | .leaf => (.leaf, .leaf)
  | .node l _ r => (l, r)

end Library.Trees.WordTree
