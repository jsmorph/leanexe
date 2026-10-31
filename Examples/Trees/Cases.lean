import Examples.Trees.Program
import TestSupport.Host

/-! Trees for the verified compiler's cases: `KeyTree.describe` writes a tree in the host's
preorder form, and `KeyTree.arbitrary` and `KeyTree.chain` build trees. -/

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

end Examples.Trees
