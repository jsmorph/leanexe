import Library.Trees.WordTree.Program
import Mathlib.Data.List.Sort

/-! The specification of Algorithm T, tree search and insertion, on `KeyTree`.  `algorithmT x t`
states the steps as a recursion on the tree and gives whether the search succeeds and the tree
afterward.  Steps T2 to T4 compare `x` with the key `k` of a node, with words compared as unsigned
numbers, and continue in the left subtree when `x < k` and in the right subtree when `k < x`.  The
search succeeds at a node with `k = x` and leaves the tree as it is.  At an empty subtree it fails,
and step T5 puts a node with `x` and two empty subtrees in that subtree's place, so the tree
afterward is the old tree with that one empty subtree replaced.  Knuth assumes a tree with at least
one node, and `algorithmT` extends his steps to the empty tree, where the search fails and the
insertion gives a tree of one node.  On a tree that is not a binary search tree, `algorithmT`
follows the same comparisons, as Knuth's steps do on any binary tree, so its search can fail for a
key that the tree holds off the path, and the insertion then adds a second node with that key.  A
binary search tree is a tree whose keys in symmetric order, `keys`, increase, so its keys are
distinct, as the keys of Knuth's tables are.  `SearchTree x t` states the guarantees that the
request asks for, and the theorem `searchTree` proves them for every binary search tree `t`: the
search succeeds exactly when `x` is a key, the tree afterward is a binary search tree, and its keys
are those of `t`, with `x` inserted in order when the search fails.  The second guarantee follows
from the third and states the request's words.  The module computes the flag with `search`, on a
tree that the caller lends, and the tree with `insert`, on a tree that the caller moves, so a
caller that needs both calls both.  The specification reads "reuse the tree's nodes" and "allocate
no node but the new one" as a bound on the rise of the heap's `top` by one node's block, which
`insert_bound` states.  The bound does not count blocks that the allocator takes from its free list,
and no statement relates the blocks of the result to those of the argument, so the program text and
the compiler's charge for every allocation show the reuse.  It reads "a call stack that does not
grow" as theorems with no call-depth premise.  That reading depends on the compiler's rule, which
the verified compiler's manual states and no theorem states: the compiler translates recognized
tail recursion into loops and gives every other recursive function and its callers a call depth,
which their theorems take as a premise. -/

namespace Library.Trees.Search

open Library.Trees.WordTree

/-- Algorithm T on the key `x` and the tree `t`: whether the search succeeds, and the tree after
the insertion of step T5 when it fails. -/
def algorithmT (x : UInt64) : KeyTree → Bool × KeyTree
  | .leaf => (false, .node .leaf x .leaf)
  | .node l k r =>
    if x < k then ((algorithmT x l).1, .node (algorithmT x l).2 k r)
    else if k < x then ((algorithmT x r).1, .node l k (algorithmT x r).2)
    else (true, .node l k r)

/-- The keys of `t` in symmetric order: those of the left subtree, the root's, and those of the
right subtree. -/
def keys : KeyTree → List UInt64
  | .leaf => []
  | .node l k r => keys l ++ k :: keys r

/-- `t` is a binary search tree: its keys in symmetric order increase. -/
def Ordered (t : KeyTree) : Prop := (keys t).Pairwise (· < ·)

/-- The guarantees of Algorithm T for the key `x` on a binary search tree `t`. -/
structure SearchTree (x : UInt64) (t : KeyTree) : Prop where
  found : (algorithmT x t).1 = true ↔ x ∈ keys t
  ordered : Ordered (algorithmT x t).2
  keys : keys (algorithmT x t).2 =
    if x ∈ keys t then keys t else (keys t).orderedInsert (· ≤ ·) x

end Library.Trees.Search
