import Library.Trees.Avl.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of balanced tree search and insertion. -/

namespace Library.Trees.Avl

open TestSupport.Host

/-- The host's preorder form of a tree of records: `.` for a leaf, and for a node its width 4, its
child mask 9, which marks the first and the last slot as children, and its slots. -/
def describe : AvlTree → String
  | .leaf => "."
  | .node l k b r => s!"4,9,{describe l},{k},{b},{describe r}"

/-- The number of nodes. -/
def size : AvlTree → Nat
  | .leaf => 0
  | .node l _ _ r => size l + 1 + size r

/-- The tree that Algorithm A builds from the empty tree by inserting `ks` in order. -/
def grow (ks : List UInt64) : AvlTree := ks.foldl (fun t k => (algorithmA k t).2) .leaf

/-- The keys `ks` as a chain of right children with factor 0 at every node, which does not match
the heights of a chain of more than one node. -/
def chain (ks : List UInt64) : AvlTree := ks.foldr (fun k t => .node .leaf k 0 t) .leaf

/-- The orders of the elements of a list. -/
def orders : List UInt64 → List (List UInt64)
  | [] => [[]]
  | a :: rest => (orders rest).flatMap fun p => (List.range (p.length + 1)).map fun i =>
    p.take i ++ a :: p.drop i

/-- The keys to search for and insert in `t`: each key of a tree of at most 16 nodes, or the first,
middle, and last keys in symmetric order of a larger tree, each with the words one below and one
above it, and the words 0, 1, `2^63 - 1`, `2^63`, and `2^64 - 1`. -/
def probes (t : AvlTree) : List UInt64 :=
  let ks := keys t
  let near := if ks.length ≤ 16 then ks else [ks.head!, ks[ks.length / 2]!, ks.getLast!]
  ((near.flatMap fun k => [k - 1, k, k + 1]) ++
    [0, 1, 9223372036854775807, 9223372036854775808, maxU]).eraseDups

/-- The distinct trees that Algorithm A builds from the orders of `ks`. -/
def builds (ks : List UInt64) : List AvlTree :=
  (orders ks).foldl (fun acc o =>
    let t := grow o
    if acc.any fun u => describe u == describe t then acc else acc ++ [t]) []

/-- The tree with the children of every node exchanged, whose keys in symmetric order are those
of `t` reversed. -/
def mirror : AvlTree → AvlTree
  | .leaf => .leaf
  | .node l k b r => .node (mirror r) k b (mirror l)

/-- The trees of the cases.  The empty tree and the distinct trees that Algorithm A builds from
every order of the keys 10 to 40, 10 to 50, and 10 to 70 in steps of 10, and from one and two keys,
hold every case of steps A7 to A9 under some probe: single rotations at the root and up to two
levels below it, double rotations at the root around a new node and around a grandchild that leans
either way, and double rotations one and two levels below the root around a new node.  Four
sequences of 10 to 16 keys build trees in which a probe causes a double rotation one or two levels
below the root around a grandchild that leans either way, in both directions.  The keys
`2^63 - 1`, `2^63`, `2^63 + 1`, and `2^64 - 1` with 0 and 1 order a tree only under unsigned
comparison.  The first 300 words of `rw`, 5,000 keys in increasing order, and 3,000 keys in
decreasing order build balanced trees of 11, 13, and 12 levels.  A chain of 3,000 right children
with factor 0 at every node, and one with factor 1 at every node, have factors that do not match
their heights, and the insertion applies the steps to the stored factors along a path of 3,000
nodes.  Five small trees hold factors that do not match their heights: the factor word 7 on either
side of a node with one child and on a node without children, a factor 1 on a node without
children, and a factor 0 on a node with only a right child.  Two trees are not search trees: a
node whose right child holds a smaller key, and the mirror image of a tree of 7 keys. -/
def avlTrees : List AvlTree :=
  let deep : List (List UInt64) :=
    [[1490, 1420, 1980, 270, 830, 110, 1050, 190, 980, 380],
      [970, 1390, 760, 1410, 650, 1830, 1230, 810, 260, 540, 1670, 820, 110, 70],
      [540, 1560, 1110, 60, 580, 50, 1020, 380, 100, 1850, 420, 1150, 1810, 1300, 1740, 1100],
      [700, 1460, 1680, 920, 1220, 1790, 630, 1600, 620, 280, 1440, 410, 300, 1990, 110, 1810]]
  let lean := (List.range 3000).foldr (fun k t => .node .leaf (UInt64.ofNat k) 1 t) .leaf
  [.leaf, grow [9223372036854775808, 9223372036854775807, maxU, 0, 9223372036854775809, 1],
    grow ((List.range 300).map rw), grow ((List.range 5000).map UInt64.ofNat),
    grow ((List.range 3000).reverse.map UInt64.ofNat),
    chain ((List.range 3000).map UInt64.ofNat), lean,
    .node (.node .leaf 3 0 .leaf) 4 7 .leaf, .node .leaf 4 7 (.node .leaf 5 0 .leaf),
    .node .leaf 2 7 .leaf, .node .leaf 2 1 .leaf, .node .leaf 10 0 (.node .leaf 20 0 .leaf),
    .node .leaf 5 0 (.node .leaf 1 0 .leaf), mirror (grow [40, 20, 60, 10, 30, 50, 70])] ++
    builds [10] ++ builds [10, 20] ++ builds [10, 20, 30, 40] ++ builds [10, 20, 30, 40, 50] ++
    builds [10, 20, 30, 40, 50, 60, 70] ++ deep.map grow

/-- The pairs of a key and a tree of the cases: each tree of `avlTrees` with each of its
`probes`. -/
def avlInputs : List (UInt64 × AvlTree) :=
  avlTrees.flatMap fun t => (probes t).map (·, t)

end Library.Trees.Avl
