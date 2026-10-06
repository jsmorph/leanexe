import Examples.Trees.Program
import Examples.Host

/-! The module cases of `trees and treeMoves`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Trees

open Examples.Host

/-- The host's preorder description of a tree: `.` for a leaf, and a node's key followed by
its subtrees. -/
def KeyTree.describe : KeyTree → String
  | .leaf => "."
  | .node l k r => s!"{k},{KeyTree.describe l},{KeyTree.describe r}"

/-- A tree of `n` nodes whose shape and keys follow the arbitrary words from `seed`. -/
def KeyTree.arbitrary : Nat → Nat → KeyTree
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
def KeyTree.chain : Nat → KeyTree
  | 0 => .leaf
  | n + 1 => .node .leaf (UInt64.ofNat n) (KeyTree.chain n)

def treeCases : IO Unit := do
  let trees : List KeyTree := [.leaf, .node .leaf 5 .leaf, .node (.node .leaf 1 .leaf) maxU .leaf,
    KeyTree.chain 999] ++ (List.range 20).map fun i => KeyTree.arbitrary (i * 3) i
  for t in trees do
    line "trees" "size" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.size)
    line "trees" "sum" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.sum)
    line "trees" "height" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.height)
    line "trees" "sizeSum" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.sizeSum)
    line "trees" "leftSizes" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.leftSizes)
    line "trees" "leftHeavy" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.leftHeavy)
    let kp := t.keyPair
    line "trees" "keyPair" "list:i64,i64" [s!"tree-u64:{KeyTree.describe t}"] s!"{kp.1},{kp.2}"
    for n in ([0, 1, 3, 10] : List UInt64) do
      line "trees" "sumSizes" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.sumSizes n))
    for xs in ([[], [7], [1, 2, 3]] : List (List UInt64)) do
      let r := t.pushSum xs.toArray
      line "trees" "pushSum" "list:array-u64,i64" [arrU xs, s!"tree-u64:{KeyTree.describe t}"]
        s!"{words r.1.toList},{r.2}"
    for n in [0, 1, 3, 10, maxU] do
      line "trees" "dropSmall" "tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.dropSmall n))
      let r := t.sizeDrop n
      line "trees" "sizeDrop" "list:i64,tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        s!"{r.1},{KeyTree.describe r.2}"
      let r2 := t.sizeDropNext n
      line "trees" "sizeDropNext" "list:i64,tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        s!"{r2.1},{KeyTree.describe r2.2}"
      line "trees" "sizeAfterDrop" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.sizeAfterDrop n))
      line "trees" "sizeDropSmall" "tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.sizeDropSmall n))
      line "trees" "sizeFirst" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.sizeFirst n))
      line "trees" "droppedSize" "i64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        (toString (t.droppedSize n))
      let r3 := t.dropWithSize n
      line "trees" "dropWithSize" "list:i64,tree-u64" [u n, s!"tree-u64:{KeyTree.describe t}"]
        s!"{r3.1},{KeyTree.describe r3.2}"
  for t in trees.take 10 do
    line "treeFrame" "wide" "i64" [s!"tree-u64:{KeyTree.describe t}"] (toString t.wide)
  for t in trees do
    for k in [0, 7, maxU] do
      line "treeMoves" "setKey" "tree-u64" [u k, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.setKey k))
    line "treeMoves" "incr" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.incr)
    for x in [0, 1, 7, 500, maxU] do
      line "treeMoves" "insert" "tree-u64" [u x, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.insert x))
    line "treeMoves" "dropRight" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.dropRight)
    line "treeMoves" "addLeft" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.addLeft)
    let sr := t.splitRoot
    line "treeMoves" "splitRoot" "list:tree-u64,tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      s!"{KeyTree.describe sr.1},{KeyTree.describe sr.2}"
    let rr := t.rootAndRest
    line "treeMoves" "rootAndRest" "list:i64,tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      s!"{rr.1},{KeyTree.describe rr.2}"
    let ko := t.keepOld
    line "treeMoves" "keepOld" "list:tree-u64,tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      s!"{KeyTree.describe ko.1},{KeyTree.describe ko.2}"
    line "treeMoves" "addSelf" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.addSelf)
    line "treeMoves" "leftChild" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.leftChild)
    for (a, b) in ([(0, 1), (7, 7), (500, maxU)] : List (UInt64 × UInt64)) do
      line "treeMoves" "insertTwo" "tree-u64" [u a, u b, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.insertTwo a b))
    for a in trees.take 4 do
      line "treeMoves" "addRoot" "tree-u64"
        [s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (a.addRoot t))
      line "treeMoves" "addAll" "tree-u64"
        [s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (a.addAll t))
      line "treeMoves" "leftSpine" "tree-u64"
        [s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (a.leftSpine t))
      let so := KeyTree.splitOr t a
      line "treeMoves" "splitOr" "list:tree-u64,tree-u64"
        [s!"tree-u64:{KeyTree.describe t}", s!"tree-u64:{KeyTree.describe a}"]
        s!"{KeyTree.describe so.1},{KeyTree.describe so.2}"
      for c in [0, 1] do
        let r := KeyTree.pickPair c a t
        line "treeMoves" "pickPair" "list:tree-u64,tree-u64"
          [u c, s!"tree-u64:{KeyTree.describe a}", s!"tree-u64:{KeyTree.describe t}"]
          s!"{KeyTree.describe r.1},{KeyTree.describe r.2}"
  -- Trees whose root's key is 0, for `trim`'s other path.
  let zeroRoots : List KeyTree := [.node .leaf 0 .leaf, .node (.node .leaf 1 .leaf) 0 (.node .leaf 2 .leaf),
    .node (KeyTree.arbitrary 5 1) 0 (KeyTree.arbitrary 6 2)]
  for t in trees ++ zeroRoots do
    for c in [0, 1, maxU] do
      line "treeMoves" "keepIf" "tree-u64" [u c, s!"tree-u64:{KeyTree.describe t}"]
        (KeyTree.describe (t.keepIf c))
    line "treeMoves" "trim" "tree-u64" [s!"tree-u64:{KeyTree.describe t}"]
      (KeyTree.describe t.trim)

def cases : IO Unit := do
  treeCases

end Examples.Trees
