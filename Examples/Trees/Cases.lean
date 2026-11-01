import Examples.Trees.Program
import TestSupport.Host

/-! Trees for the verified compiler's cases: `KeyTree.describe` writes a tree in the host's
preorder form, `KeyTree.arbitrary`, `KeyTree.chain`, and `KeyTree.leftChain` build trees, and
`keyTreeArgs` and `keyTreePairs` are the inputs of the cases of `exampleTrees`, whose call depths
`KeyTree.spine` and `KeyTree.searchDepth` give. -/

namespace Examples.Trees

open TestSupport.Host

/-- The host's preorder description of a tree: `.` for a leaf, and a node's key followed by
its subtrees. -/
def KeyTree.describe : Library.Trees.WordTree.KeyTree → String
  | .leaf => "."
  | .node l k r => s!"{k},{KeyTree.describe l},{KeyTree.describe r}"

/-- A tree of `n` nodes whose shape and keys follow the arbitrary words from `seed`. -/
def KeyTree.arbitrary : Nat → Nat → Library.Trees.WordTree.KeyTree
  | 0, _ => .leaf
  | n + 1, seed =>
    let left := (rw seed).toNat % (n + 1)
    .node (KeyTree.arbitrary left (2 * seed + 1)) (rw (seed + 7)) (KeyTree.arbitrary (n - left) (2 * seed + 2))
termination_by n => n
decreasing_by
  all_goals
    have := Nat.mod_lt (rw seed).toNat (Nat.succ_pos n)
    omega

/-- A chain of `n` nodes, each with a leaf on the left. -/
def KeyTree.chain : Nat → Library.Trees.WordTree.KeyTree
  | 0 => .leaf
  | n + 1 => .node .leaf (UInt64.ofNat n) (KeyTree.chain n)

/-- A chain of `n` nodes, each with a leaf on the right. -/
def KeyTree.leftChain : Nat → Library.Trees.WordTree.KeyTree
  | 0 => .leaf
  | n + 1 => .node (KeyTree.leftChain n) (UInt64.ofNat n) .leaf

/-- The number of nodes on the path of left children from the root, the depth of the deepest
call of `leftSpine` below its first. -/
def KeyTree.spine : Library.Trees.WordTree.KeyTree → Nat
  | .leaf => 0
  | .node l _ _ => KeyTree.spine l + 1

/-- The number of nodes that `insert x` passes before it reaches a leaf or the node that holds
`x`, the depth of the deepest call of `insert x` below its first. -/
def KeyTree.searchDepth (x : UInt64) : Library.Trees.WordTree.KeyTree → Nat
  | .leaf => 0
  | .node l k r =>
    if x < k then KeyTree.searchDepth x l + 1 else if k < x then KeyTree.searchDepth x r + 1 else 0

/-- The trees of the cases of `exampleTrees`: a leaf, a node with key 0, two trees of three nodes,
chains on either side at the call-depth limit and of 4,096 nodes, and arbitrary trees. -/
def keyTreeArgs : List Library.Trees.WordTree.KeyTree :=
  [.leaf, .node .leaf 0 .leaf, .node (.node .leaf 1 .leaf) 5 (.node .leaf 9 .leaf),
      .node (.node .leaf 3 .leaf) 0 (.node .leaf 4 .leaf)] ++
    [997, 998, 999, 1000, 4096].map KeyTree.chain ++ [998, 999, 1000].map KeyTree.leftChain ++
    (List.range 12).map fun i => KeyTree.arbitrary (3 * i + 1) (i + 40)

/-- The pairs of trees of the cases of `exampleTrees`: every pair of six small trees, and a tree of
three nodes with chains on either side at the call-depth limit and of 4,096 nodes. -/
def keyTreePairs : List (Library.Trees.WordTree.KeyTree × Library.Trees.WordTree.KeyTree) :=
  let small := keyTreeArgs.take 4 ++ [KeyTree.arbitrary 9 3, KeyTree.arbitrary 30 5]
  let guide : Library.Trees.WordTree.KeyTree := .node (.node .leaf 1 .leaf) 5 (.node .leaf 9 .leaf)
  (small.flatMap fun a => small.map fun b => (a, b)) ++
    [999, 1000, 4096].flatMap fun m => [(guide, KeyTree.chain m), (guide, KeyTree.leftChain m)]

end Examples.Trees
