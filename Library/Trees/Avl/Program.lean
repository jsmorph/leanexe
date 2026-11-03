/-! Balanced tree search and insertion, Knuth's Algorithm A of TAOCP §6.2.3, on `AvlTree`, a
binary tree whose node holds a key and Knuth's balance factor `B`, the height of the right subtree
minus the height of the left subtree, as a word: 0, 1, or `2^64 - 1` for −1.  `search` follows the
comparisons from the root.  `insert` follows the same path in `descend`, reversing each link that
it passes as `Library.Trees.Search.insert` does, puts a new node at the end of the path or keeps
the node that holds `x`, and returns in `ascend`, which restores the links and adjusts the balance
factors.  While the subtree below a node has grown, `ascend` applies steps A6 and A7 at that node:
a node with the opposite factor becomes balanced and the growth stops, a balanced node takes the
factor of the side that grew, and a node with any other factor is rotated by step A8 or A9, which
also stops the growth. -/

namespace Library.Trees.Avl

/-- A binary tree with a key and a balance factor at each node. -/
inductive AvlTree where
  | leaf
  | node (left : AvlTree) (key : UInt64) (balance : UInt64) (right : AvlTree)

/-- Steps A1 to A4: whether a node on the path of comparisons from the root holds `x`. -/
def search (x : UInt64) : AvlTree → Bool
  | .leaf => false
  | .node l k _ r => if x < k then search x l else if k < x then search x r else true

/-- Steps A8 and A9 at a node whose left subtree has grown two levels above its right subtree: a
single rotation when the left subtree is higher on its left, and a double rotation when it is higher
on its right.  The rotation destructures the node, so that each node it builds can take the block of
a node it consumed. -/
def rotateRight (s : AvlTree) : AvlTree :=
  match s with
  | .leaf => .leaf
  | .node t k b c =>
    match t with
    | .leaf => .node .leaf k b c
    | .node tl tk tb tr =>
      if tb = 0 - 1 then .node tl tk 0 (.node tr k 0 c)
      else
        match tr with
        | .leaf => .node (.node tl tk tb .leaf) k b c
        | .node ul uk ub ur =>
          .node (.node tl tk (if ub = 1 then 0 - 1 else 0) ul) uk 0
            (.node ur k (if ub = 0 - 1 then 1 else 0) c)

/-- Steps A8 and A9 at a node whose right subtree has grown two levels above its left subtree. -/
def rotateLeft (s : AvlTree) : AvlTree :=
  match s with
  | .leaf => .leaf
  | .node a k b t =>
    match t with
    | .leaf => .node a k b .leaf
    | .node tl tk tb tr =>
      if tb = 1 then .node (.node a k 0 tl) tk 0 tr
      else
        match tl with
        | .leaf => .node a k b (.node .leaf tk tb tr)
        | .node ul uk ub ur =>
          .node (.node a k (if ub = 1 then 0 - 1 else 0) ul) uk 0
            (.node ur tk (if ub = 0 - 1 then 1 else 0) tr)

/-- The return from the end of the path: `path` holds the nodes above `t`, each with the rest of
the path in its left field when `x` is less than its key and in its right field otherwise.  When
`grew` holds, steps A6 and A7 adjust the node above `t`, and on a balanced tree `t` is then one
level higher than the subtree it replaces. -/
def ascend (x : UInt64) (grew : Bool) (path t : AvlTree) : AvlTree :=
  match path with
  | .leaf => t
  | .node a k b c =>
    if x < k then
      if grew then
        if b = 1 then ascend x false a (.node t k 0 c)
        else if b = 0 then ascend x true a (.node t k (0 - 1) c)
        else ascend x false a (rotateRight (.node t k b c))
      else ascend x false a (.node t k b c)
    else
      if grew then
        if b = 0 - 1 then ascend x false c (.node a k 0 t)
        else if b = 0 then ascend x true c (.node a k 1 t)
        else ascend x false c (rotateLeft (.node a k b t))
      else ascend x false c (.node a k b t)

/-- Steps A2 to A5 from the root of `t`, with the nodes above `t` in `path`. -/
def descend (x : UInt64) (path t : AvlTree) : AvlTree :=
  match t with
  | .leaf => ascend x true path (.node .leaf x 0 .leaf)
  | .node l k b r =>
    if x < k then descend x (.node path k b r) l
    else if k < x then descend x (.node l k b path) r
    else ascend x false path (.node l k b r)

/-- Algorithm A's insertion: `t` with a new node that holds `x` at the end of the path of
comparisons and the factors adjusted by steps A6 to A9, which restore the balance of a balanced
tree, or `t` when a node on the path holds `x`. -/
def insert (x : UInt64) (t : AvlTree) : AvlTree := descend x .leaf t

end Library.Trees.Avl
