import Library.Trees.Avl.Spec

/-! The specification of deletion from a balanced tree, on the `AvlTree` of Algorithm A.
`deleteA x t` states the deletion as a recursion on the tree and gives a flag and the tree
afterward, and on a balanced tree the flag records whether the tree shrank one level.  The search
compares `x` with the key `k` of a node, with words compared as unsigned numbers, and continues in
the left subtree when `x < k` and in the right subtree when `k < x`, so with repeated keys it stops
at the first node with `k = x` on the path.  When it reaches an empty subtree, the tree stays as it
is, factors included, whatever its shape.  The node with `k = x` is replaced by its right subtree
when its left subtree is empty and by its left subtree when its right subtree is empty.  Otherwise
it keeps its place and its factor and takes the key of the leftmost node of its right subtree, which
`deleteMinA` replaces by that node's right subtree; on a search tree that key is the successor of
`x`.  TAOCP §6.2.2, Algorithm D, tests only the right link in step D1 and moves the successor's node
into the place of the deleted node, and on a balanced tree the two methods give the same tree.  A
removed node shrinks its subtree by one level.  When the subtree on one side of a node has shrunk,
`shrinkLeftA` or `shrinkRightA` adjusts the node, as §6.2.3 describes: a node that was higher on
that side becomes balanced and shrinks, a balanced node becomes higher on the other side and keeps
its height, and a node that was higher on the other side is rotated.  The rotation is single when
the child on the other side is balanced or leans away from the shrunk side, and it keeps the node's
height when that child was balanced and shrinks it otherwise.  It is double otherwise, with the
factors of Algorithm A's step A9, and it shrinks the node.  On a tree whose factors do not match its
heights, `deleteA` applies the same rules to the stored factors, and its flag need not record
whether the tree shrank.  A factor word other than 0, 1, and `2^64 - 1` counts as a lean to the
other side at the node, selects the double rotation at the child, and gives both new factors 0 at
the grandchild.  A node that would rotate but has no child on the other side, or no inner grandchild
for a double rotation, keeps its factor and does not shrink.  `Removes x t` states the guarantees,
and the theorem `removes` proves them for every balanced binary search tree `t`: the tree afterward
is a balanced binary search tree, its keys are those of `t` without `x`, it stays as it is when `x`
is not a key, and it shrank one level exactly when `deleteA` reports it, which happens only when `x`
is a key of `t`.  `deleteA_of_searchA` states that a failed search leaves every tree as it is.
Knuth keeps the tree's height in a head node, and the module keeps no head node. -/

namespace Library.Trees.AvlDelete

open Library.Trees.Avl (AvlTree height keys Ordered Balanced)

/-- The node with left subtree `t`, key `k`, factor `b`, and right subtree `c`, after `t` has shrunk
one level: whether the node shrank, and the node. -/
def shrinkLeftA (t : AvlTree) (k b : UInt64) (c : AvlTree) : Bool × AvlTree :=
  if b = 0 - 1 then (true, .node t k 0 c)
  else if b = 0 then (false, .node t k 1 c)
  else match c with
    | .node cl ck cb cr =>
      if cb = 0 then (false, .node (.node t k 1 cl) ck (0 - 1) cr)
      else if cb = 1 then (true, .node (.node t k 0 cl) ck 0 cr)
      else match cl with
        | .node ul uk ub ur =>
          (true, .node (.node t k (if ub = 1 then 0 - 1 else 0) ul) uk 0
            (.node ur ck (if ub = 0 - 1 then 1 else 0) cr))
        | .leaf => (false, .node t k b c)
    | .leaf => (false, .node t k b c)

/-- The node with left subtree `a`, key `k`, factor `b`, and right subtree `t`, after `t` has shrunk
one level. -/
def shrinkRightA (a : AvlTree) (k b : UInt64) (t : AvlTree) : Bool × AvlTree :=
  if b = 1 then (true, .node a k 0 t)
  else if b = 0 then (false, .node a k (0 - 1) t)
  else match a with
    | .node al ak ab ar =>
      if ab = 0 then (false, .node al ak 1 (.node ar k (0 - 1) t))
      else if ab = 0 - 1 then (true, .node al ak 0 (.node ar k 0 t))
      else match ar with
        | .node ul uk ub ur =>
          (true, .node (.node al ak (if ub = 1 then 0 - 1 else 0) ul) uk 0
            (.node ur k (if ub = 0 - 1 then 1 else 0) t))
        | .leaf => (false, .node a k b t)
    | .leaf => (false, .node a k b t)

/-- The removal of the leftmost node of `t`: whether the tree shrank, the node's key, which is the
least key of a search tree, and the tree, which is `t` with that node replaced by its right
subtree. -/
def deleteMinA : AvlTree → Bool × UInt64 × AvlTree
  | .leaf => (false, 0, .leaf)
  | .node .leaf k _ r => (true, k, r)
  | .node (.node ll lk lb lr) k b r =>
    let d := deleteMinA (.node ll lk lb lr)
    if d.1 then ((shrinkLeftA d.2.2 k b r).1, d.2.1, (shrinkLeftA d.2.2 k b r).2)
    else (false, d.2.1, .node d.2.2 k b r)

/-- The deletion of `x` from `t`: whether the tree shrank one level, and the tree. -/
def deleteA (x : UInt64) : AvlTree → Bool × AvlTree
  | .leaf => (false, .leaf)
  | .node l k b r =>
    if x < k then
      if (deleteA x l).1 then shrinkLeftA (deleteA x l).2 k b r
      else (false, .node (deleteA x l).2 k b r)
    else if k < x then
      if (deleteA x r).1 then shrinkRightA l k b (deleteA x r).2
      else (false, .node l k b (deleteA x r).2)
    else match l, r with
      | .leaf, _ => (true, r)
      | _, .leaf => (true, l)
      | _, _ =>
        if (deleteMinA r).1 then shrinkRightA l (deleteMinA r).2.1 b (deleteMinA r).2.2
        else (false, .node l (deleteMinA r).2.1 b (deleteMinA r).2.2)

/-- The guarantees of deletion for the key `x` on a balanced binary search tree `t`. -/
structure Removes (x : UInt64) (t : AvlTree) : Prop where
  ordered : Ordered (deleteA x t).2
  balanced : Balanced (deleteA x t).2
  keyList : keys (deleteA x t).2 = (keys t).erase x
  heightAfter : height (deleteA x t).2 + (if (deleteA x t).1 then 1 else 0) = height t
  shrank : (deleteA x t).1 = true → x ∈ keys t
  unchanged : x ∉ keys t → (deleteA x t).2 = t

end Library.Trees.AvlDelete
