import Library.Trees.WordTree.Program

/-! Knuth's Algorithm T, tree search and insertion, on `KeyTree`, with no recursion other than
tail recursion.  `search` follows steps T1 to T4 from the root.  `insert` follows the same path in
`descend` and reverses each link that it passes: the node that it leaves holds the path above it in
the field of the child it moves to.  At the end of the path `descend` places a new node with `x`,
step T5, or keeps the node that holds `x`, and `ascend` restores the links on the way back to the
root.  A comparison of `x` with a node's key determines, for `ascend`, which field holds the path,
so the reversed nodes need no other mark, and each step rebuilds the node that it destructures. -/

namespace Library.Trees.Search

open Library.Trees.WordTree

/-- Steps T1 to T4: whether a node on the path of comparisons from the root holds `x`. -/
def search (x : UInt64) : KeyTree → Bool
  | .leaf => false
  | .node l k r => if x < k then search x l else if k < x then search x r else true

/-- The return from the end of the path: `path` holds the nodes above `t`, each with the rest of
the path in its left field when `x` is less than its key and in its right field otherwise, and
`ascend` restores each node's link to the subtree below it. -/
def ascend (x : UInt64) (path t : KeyTree) : KeyTree :=
  match path with
  | .leaf => t
  | .node a k b => if x < k then ascend x a (.node t k b) else ascend x b (.node a k t)

/-- Steps T2 to T5 from the root of `t`, with the nodes above `t` in `path`. -/
def descend (x : UInt64) (path t : KeyTree) : KeyTree :=
  match t with
  | .leaf => ascend x path (.node .leaf x .leaf)
  | .node l k r =>
    if x < k then descend x (.node path k r) l
    else if k < x then descend x (.node l k path) r
    else ascend x path (.node l k r)

/-- Algorithm T's insertion: `t` with a new node that holds `x` at the end of the path of
comparisons, or `t` when a node on the path holds `x`. -/
def insert (x : UInt64) (t : KeyTree) : KeyTree := descend x .leaf t

end Library.Trees.Search
