import Library.Trees.Search.Spec
import Examples.Trees.Cases

/-! The inputs of the verified compiler's cases of tree search and insertion. -/

namespace Library.Trees.Search

open TestSupport.Host Library.Trees.WordTree

/-- The tree that Algorithm T builds from the empty tree by inserting `ks` in order. -/
def grow (ks : List UInt64) : KeyTree := ks.foldl (fun t k => (algorithmT k t).2) .leaf

/-- The keys `ks` as a chain of right children, which `grow ks` builds when `ks` increases. -/
def rightChain (ks : List UInt64) : KeyTree := ks.foldr (fun k t => .node .leaf k t) .leaf

/-- The keys `ks` as a chain of left children with the last key at the root, which
`grow ks.reverse` builds when `ks` increases. -/
def leftChain (ks : List UInt64) : KeyTree := ks.foldl (fun t k => .node t k .leaf) .leaf

/-- The tree with the children of every node exchanged, whose keys in symmetric order are those
of `t` reversed. -/
def mirror : KeyTree → KeyTree
  | .leaf => .leaf
  | .node l k r => .node (mirror r) k (mirror l)

/-- The keys to search for and insert in `t`: each key of a tree of at most 12 nodes, or the first,
middle, and last keys in symmetric order of a larger tree, each with the words one below and one
above it, and the words 0, 1, `2^63 - 1`, `2^63`, and `2^64 - 1`. -/
def probes (t : KeyTree) : List UInt64 :=
  let ks := keys t
  let near := if ks.length ≤ 12 then ks else [ks.head!, ks[ks.length / 2]!, ks.getLast!]
  ((near.flatMap fun k => [k - 1, k, k + 1]) ++
    [0, 1, 9223372036854775807, 9223372036854775808, maxU]).eraseDups

/-- The trees of the cases.  The empty tree, one node, and seven nodes in three levels are search
trees, and so are the chains that `grow` builds from three keys in increasing and decreasing order
and the tree of three keys with its root in the middle.  The keys `2^63 - 1`, `2^63`, `2^63 + 1`,
and `2^64 - 1` with 0 and 1 form a search tree under unsigned comparison only.  The first 300
words of `rw` form a search tree of 12 levels.  A chain of 1,000 right children has a path of 1,000
nodes, the limit of nested calls of the compiler's guarded recursion, and chains of 10,000 keys
have paths ten times longer: the left chain holds the keys 1 to 10,000, so that the key 0 passes
10,000 left children.  `grow` builds from the keys 0, `2^64 - 1`, 1, `2^64 - 2`, and so on, 2,000
in all, a search tree whose deepest path of 2,000 nodes changes direction at every node.  The
mirror image of the seven nodes and the arbitrary trees of 5 to 17 nodes with arbitrary keys are
not search trees, and the comparisons pass by keys that they hold.  The arbitrary tree of 2 nodes is
a search tree under unsigned comparison.  Two trees hold equal keys: three nodes with the key 5,
where the search for 5 stops at the root, and the chain of 3, 5, and 5, where it stops at the
first 5 below the root. -/
def searchTrees : List KeyTree :=
  let seven := grow [5, 3, 8, 1, 4, 7, 9]
  let thousands := (List.range 10000).map UInt64.ofNat
  let zigzag := (List.range 1000).flatMap fun i => [UInt64.ofNat i, maxU - UInt64.ofNat i]
  [.leaf, .node .leaf 5 .leaf, seven, grow [1, 2, 3], grow [3, 2, 1], grow [2, 1, 3],
    grow [9223372036854775808, 9223372036854775807, maxU, 0, 9223372036854775809, 1],
    grow ((List.range 300).map rw), rightChain ((List.range 1000).map UInt64.ofNat),
    rightChain thousands, leftChain (thousands.map (· + 1)), grow zigzag, mirror seven,
    .node (.node .leaf 5 .leaf) 5 (.node .leaf 5 .leaf),
    .node .leaf 3 (.node .leaf 5 (.node .leaf 5 .leaf))] ++
    (List.range 6).map fun i => Examples.Trees.KeyTree.arbitrary (3 * i + 2) (i + 70)

/-- The pairs of a key and a tree of the cases: each tree of `searchTrees` with each of its
`probes`. -/
def searchInputs : List (UInt64 × KeyTree) :=
  searchTrees.flatMap fun t => (probes t).map (·, t)

end Library.Trees.Search
