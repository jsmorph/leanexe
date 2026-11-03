import Library.Trees.Avl.Program
import Mathlib.Data.List.Sort

/-! The specification of Algorithm A, balanced tree search and insertion, on `AvlTree`.  A node's
balance factor `B` is the height of its right subtree minus the height of its left subtree, as a
word, with −1 written `2^64 - 1`.  `Balanced t` states that at every node the heights of the
subtrees differ by at most 1 and the stored factor is their difference.  `algorithmA x t` states the
insertion as a recursion on the tree and gives a flag and the tree afterward, and on a balanced tree
the flag records whether the tree grew one level.  Steps A2 to A4 compare `x` with the key `k` of a
node, with words compared as unsigned numbers, and continue in the left subtree when `x < k` and in
the right subtree when `k < x`.  A node with `k = x` ends the search, and the tree stays as it is.
At an empty subtree, step A5 puts a node with `x`, factor 0, and two empty subtrees in its place,
which grows that subtree.  When the subtree on one side of a node has grown, steps A6 and A7 adjust
the node: a node that leaned to the other side becomes balanced and the growth stops, a balanced
node leans to the side that grew and grows, and a node that leaned to the same side is rotated,
which stops the growth.  Step A8 rotates the node single when the subtree that grew leans the same
way, and step A9 rotates it double around the grandchild on the inner side otherwise, with the
factors of Knuth's step.  Knuth assumes a tree with at least one node and a head node above the
root, whose link field counts the height, and `algorithmA` extends his steps to the empty tree,
where the insertion gives a tree of one node, and keeps no head node.  On a tree whose factors do
not match its heights, `algorithmA` applies the same rules to the stored factors and gives Knuth's
result wherever his steps apply, and its flag need not record whether the tree grew.  Two choices
cover the trees where his steps do not apply.  A factor word other than 0, 1, and `2^64 - 1` counts
as a lean toward the side that grew, so the node is rotated.  A node that leans toward the side that
grew, whose grown subtree is a single new node or has no grandchild on the inner side when one is
needed, keeps its factor, and the growth stops.  On a tree whose keys in symmetric order do not
increase, the search follows the same comparisons and can pass by a key that the tree holds.
`searchA x t` states the search of steps A1 to A4.  `SearchTree x t` states the guarantees, and the
theorem `searchTree` proves them for every balanced binary search tree `t`: the search succeeds
exactly when `x` is a key, the tree afterward is a balanced binary search tree, its keys are those
of `t` with `x` inserted in order when the search fails, and it grew one level exactly when
`algorithmA` reports growth, which happens only when the search fails.  The module computes the flag
of the search with `search` and the tree of the insertion with `insert`, which does not report
whether it found the key. -/

namespace Library.Trees.Avl

/-- The number of nodes on the longest path from the root. -/
def height : AvlTree → Nat
  | .leaf => 0
  | .node l _ _ r => max (height l) (height r) + 1

/-- The keys in symmetric order: those of the left subtree, the root's, and those of the right
subtree. -/
def keys : AvlTree → List UInt64
  | .leaf => []
  | .node l k _ r => keys l ++ k :: keys r

/-- `t` is a binary search tree: its keys in symmetric order increase. -/
def Ordered (t : AvlTree) : Prop := (keys t).Pairwise (· < ·)

/-- At every node the heights of the subtrees differ by at most 1, and the factor is the right
height minus the left height. -/
def Balanced : AvlTree → Prop
  | .leaf => True
  | .node l _ b r => Balanced l ∧ Balanced r ∧
      (height r = height l ∧ b = 0 ∨ height r = height l + 1 ∧ b = 1 ∨
        height l = height r + 1 ∧ b = 0 - 1)

/-- Steps A1 to A4: whether a node on the path of comparisons holds `x`. -/
def searchA (x : UInt64) : AvlTree → Bool
  | .leaf => false
  | .node l k _ r => if x < k then searchA x l else if k < x then searchA x r else true

/-- The node with left subtree `t`, key `k`, and right subtree `c`, after `t` has grown: steps A6
to A9 for a node whose factor before the growth was `b`.  On a balanced tree, the flag of the
result records whether the node grew. -/
def growLeft (t : AvlTree) (k b : UInt64) (c : AvlTree) : Bool × AvlTree :=
  if b = 1 then (false, .node t k 0 c)
  else if b = 0 then (true, .node t k (0 - 1) c)
  else match t with
    | .node tl tk tb tr =>
      if tb = 0 - 1 then (false, .node tl tk 0 (.node tr k 0 c))
      else match tr with
        | .node ul uk ub ur =>
          (false, .node (.node tl tk (if ub = 1 then 0 - 1 else 0) ul) uk 0
            (.node ur k (if ub = 0 - 1 then 1 else 0) c))
        | .leaf => (false, .node t k b c)
    | .leaf => (false, .node t k b c)

/-- The node with left subtree `a`, key `k`, and right subtree `t`, after `t` has grown. -/
def growRight (a : AvlTree) (k b : UInt64) (t : AvlTree) : Bool × AvlTree :=
  if b = 0 - 1 then (false, .node a k 0 t)
  else if b = 0 then (true, .node a k 1 t)
  else match t with
    | .node tl tk tb tr =>
      if tb = 1 then (false, .node (.node a k 0 tl) tk 0 tr)
      else match tl with
        | .node ul uk ub ur =>
          (false, .node (.node a k (if ub = 1 then 0 - 1 else 0) ul) uk 0
            (.node ur tk (if ub = 0 - 1 then 1 else 0) tr))
        | .leaf => (false, .node a k b t)
    | .leaf => (false, .node a k b t)

/-- Algorithm A's insertion of `x` into `t`: a flag that records, on a balanced tree, whether the
tree grew one level, and the tree. -/
def algorithmA (x : UInt64) : AvlTree → Bool × AvlTree
  | .leaf => (true, .node .leaf x 0 .leaf)
  | .node l k b r =>
    if x < k then
      if (algorithmA x l).1 then growLeft (algorithmA x l).2 k b r
      else (false, .node (algorithmA x l).2 k b r)
    else if k < x then
      if (algorithmA x r).1 then growRight l k b (algorithmA x r).2
      else (false, .node l k b (algorithmA x r).2)
    else (false, .node l k b r)

/-- The guarantees of Algorithm A for the key `x` on a balanced binary search tree `t`. -/
structure SearchTree (x : UInt64) (t : AvlTree) : Prop where
  found : searchA x t = true ↔ x ∈ keys t
  ordered : Ordered (algorithmA x t).2
  balanced : Balanced (algorithmA x t).2
  keyList : keys (algorithmA x t).2 =
    if x ∈ keys t then keys t else (keys t).orderedInsert (· ≤ ·) x
  heightAfter : height (algorithmA x t).2 = height t + if (algorithmA x t).1 then 1 else 0
  grew : (algorithmA x t).1 = true → x ∉ keys t

end Library.Trees.Avl
