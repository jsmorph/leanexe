import Library.Trees.Avl.Program

/-! Deletion from a balanced tree, on the `AvlTree` of Algorithm A.  A node with an empty subtree
gives way to its other subtree, and a node with two subtrees takes the key of the leftmost node of
its right subtree, its successor on a search tree, whose node gives way to its right subtree, the
symmetric form of the deletion of TAOCP §6.2.2, Algorithm D.  §6.2.3 restores the balance on the
way back to the root.  `descendDel` follows the path of comparisons to `x`, reversing each link
that it passes as the insertion does.  When the node with `x` has two subtrees, `minDel` follows
the left links of its right subtree to the successor, reversing them as well, and takes the node
with `x` as an argument, with the path above it in its right field.  `ascendMin` and `ascendDel`
restore the links on the way back.  While the subtree below a node has shrunk one level,
`shrinkLeft` and `shrinkRight` adjust the node: a node that leaned toward the side that shrank
becomes balanced and shrinks, a balanced node leans to the other side and keeps its height, and on a
balanced tree a node that leaned to the other side is rotated single or double, which keeps its
height when the single rotation's child was balanced and shrinks it otherwise. -/

namespace Library.Trees.AvlDelete

open Library.Trees.Avl (AvlTree)

/-- Whether `t` is empty. -/
def isLeaf (t : AvlTree) : Bool :=
  match t with
  | .leaf => true
  | .node _ _ _ _ => false

/-- The node `s` after its left subtree has shrunk one level: whether the node shrank, and the
node. -/
def shrinkLeft (s : AvlTree) : Bool × AvlTree :=
  match s with
  | .leaf => (false, .leaf)
  | .node t k b c =>
    if b = 0 - 1 then (true, .node t k 0 c)
    else if b = 0 then (false, .node t k 1 c)
    else
      match c with
      | .leaf => (false, .node t k b .leaf)
      | .node cl ck cb cr =>
        if cb = 0 then (false, .node (.node t k 1 cl) ck (0 - 1) cr)
        else if cb = 1 then (true, .node (.node t k 0 cl) ck 0 cr)
        else
          match cl with
          | .leaf => (false, .node t k b (.node .leaf ck cb cr))
          | .node ul uk ub ur =>
            (true, .node (.node t k (if ub = 1 then 0 - 1 else 0) ul) uk 0
              (.node ur ck (if ub = 0 - 1 then 1 else 0) cr))

/-- The node `s` after its right subtree has shrunk one level. -/
def shrinkRight (s : AvlTree) : Bool × AvlTree :=
  match s with
  | .leaf => (false, .leaf)
  | .node a k b t =>
    if b = 1 then (true, .node a k 0 t)
    else if b = 0 then (false, .node a k (0 - 1) t)
    else
      match a with
      | .leaf => (false, .node .leaf k b t)
      | .node al ak ab ar =>
        if ab = 0 then (false, .node al ak 1 (.node ar k (0 - 1) t))
        else if ab = 0 - 1 then (true, .node al ak 0 (.node ar k 0 t))
        else
          match ar with
          | .leaf => (false, .node (.node al ak ab .leaf) k b t)
          | .node ul uk ub ur =>
            (true, .node (.node al ak (if ub = 1 then 0 - 1 else 0) ul) uk 0
              (.node ur k (if ub = 0 - 1 then 1 else 0) t))

/-- The return from a removal along the path of comparisons: `path` holds the nodes above `t`, each
with the rest of the path in its left field when `x` is less than its key and in its right field
otherwise.  When `shrunk` holds, the node above `t` is adjusted. -/
def ascendDel (x : UInt64) (shrunk : Bool) (path t : AvlTree) : AvlTree :=
  match path with
  | .leaf => t
  | .node a k b c =>
    if x < k then
      if shrunk then
        let r := shrinkLeft (.node t k b c)
        ascendDel x r.1 a r.2
      else ascendDel x false a (.node t k b c)
    else
      if shrunk then
        let r := shrinkRight (.node a k b t)
        ascendDel x r.1 c r.2
      else ascendDel x false c (.node a k b t)

/-- The return from the successor: `inner` holds the nodes between the node with `x` and `t`, each
with the rest of `inner` in its left field, and `found` is the node with `x`, with its left
subtree in its left field and the path above it in its right field.  At the end of `inner`, the
node with `x` takes the successor's key `s`. -/
def ascendMin (x s : UInt64) (shrunk : Bool) (found inner t : AvlTree) : AvlTree :=
  match inner with
  | .leaf =>
    match found with
    | .leaf => t
    | .node a _ b path =>
      if shrunk then
        let r := shrinkRight (.node a s b t)
        ascendDel x r.1 path r.2
      else ascendDel x false path (.node a s b t)
  | .node i k b c =>
    if shrunk then
      let r := shrinkLeft (.node t k b c)
      ascendMin x s r.1 found i r.2
    else ascendMin x s false found i (.node t k b c)

/-- The search for the successor along the left links of `t`, with the nodes above `t` in `inner`:
the node without a left subtree gives its key and is replaced by its right subtree. -/
def minDel (x : UInt64) (found inner t : AvlTree) : AvlTree :=
  match t with
  | .leaf => ascendMin x 0 false found inner .leaf
  | .node l k b r =>
    if isLeaf l then ascendMin x k true found inner r
    else minDel x found (.node inner k b r) l

/-- The search for `x` from the root of `t`, with the nodes above `t` in `path`. -/
def descendDel (x : UInt64) (path t : AvlTree) : AvlTree :=
  match t with
  | .leaf => ascendDel x false path .leaf
  | .node l k b r =>
    if x < k then descendDel x (.node path k b r) l
    else if k < x then descendDel x (.node l k b path) r
    else if isLeaf l then ascendDel x true path r
    else if isLeaf r then ascendDel x true path l
    else minDel x (.node l k b path) .leaf r

/-- The deletion of `x` from `t`: `t` without the key `x`, with the factors adjusted by the steps
that restore the balance of a balanced tree, or `t` when no node on the path of comparisons holds
`x`.  A node with `x` and two subtrees keeps its block and takes its successor's key. -/
def delete (x : UInt64) (t : AvlTree) : AvlTree := descendDel x .leaf t

end Library.Trees.AvlDelete
