import Library.Trees.AvlDelete.Spec
import TestSupport.Modules.Avl

/-! The inputs of the verified compiler's cases of deletion from a balanced tree. -/

namespace Library.Trees.AvlDelete

open TestSupport.Host Library.Trees.Avl

/-- The keys to delete from `t`: each key of a tree of at most 40 nodes, or the first, middle, and
last keys in symmetric order of a larger tree, each with the words one below and one above it, and
the words 0, 1, `2^63 - 1`, `2^63`, and `2^64 - 1`. -/
def deleteProbes (t : AvlTree) : List UInt64 :=
  let ks := keys t
  let near := if ks.length ≤ 40 then ks else [ks.head!, ks[ks.length / 2]!, ks.getLast!]
  ((near.flatMap fun k => [k - 1, k, k + 1]) ++
    [0, 1, 9223372036854775807, 9223372036854775808, maxU]).eraseDups

/-- The tree with every factor replaced by `b`. -/
def setFactors (b : UInt64) : AvlTree → AvlTree
  | .leaf => .leaf
  | .node l k _ r => .node (setFactors b l) k b (setFactors b r)

/-- The trees of the cases: the trees of the insertion's cases, and the trees that Algorithm A
builds from twelve sequences of 5 to 38 keys.  The deletions of these trees' keys pass through
every case of a shrunk subtree that occurs on a balanced tree, at every location and depth: on the
path to the key, at the node that takes its successor's key, and on the path to the successor, on
either side, at the root and one, two, and three or more levels below it.  The cases are a node
that leaned toward the shrunk side, a balanced node, a single rotation around a balanced child or
a child that leans away from the shrunk side, and a double rotation around a grandchild that leans
either way or is balanced.  A Python model of `deleteA` counts 105 such combinations in random
balanced trees of up to 70 keys and finds each in the cases.  Six trees hold factors that do not
match their heights or keys that repeat: a child with the factor word 7 in a rotation, a node with
the factor word 7 and two children, a node that leans right with no inner grandchild, a node below
the root that leans right with no right child, a tree of 7 keys with factor 1 at every node, which
reaches rotations and a successor search on the stored factors, and three nodes with the key 5. -/
def deleteTrees : List AvlTree :=
  let sequences : List (List UInt64) :=
    [[3710, 550, 2720, 3490, 770, 690, 1740, 230, 530, 3450, 3910, 2210, 2890, 2160, 2450, 1920,
        2760, 2680, 3320, 1750, 3610, 2590, 3100, 2970, 2220, 870, 370, 1890, 1910, 1010, 2780,
        810, 1400, 3570, 1470, 2360, 1310, 2410],
      [370, 3510, 1230, 3780, 450, 330, 1130, 3430, 1710, 3360, 2390, 630, 3900, 2670, 1340, 780,
        3250, 2890, 420, 130, 1800, 710, 1280, 60, 2480, 1160, 1370, 3350, 2370, 1440, 170, 3940,
        2780, 2520, 3420, 3770, 2640, 3980],
      [1380, 3080, 720, 2160, 70, 3780, 2720, 2400, 2200, 3470, 830, 920],
      [1010, 1120, 150, 3030, 1410, 1570, 2080, 2600, 2520, 3040, 490, 2100],
      [3350, 900, 2790, 910, 3860, 90, 3590, 2410, 310, 2770, 630, 3990, 840, 3500, 3960, 2160,
        1890, 1120, 3820, 1260, 1760],
      [3070, 530, 1170, 1930, 1040, 2280, 1920, 1720],
      [450, 1990, 1270, 2180, 2090, 1110, 220, 3160, 3140, 2400, 3950, 2950, 1220, 1720, 260,
        3910, 280, 3450, 60, 380, 1750],
      [1100, 150, 3320, 3110, 3150, 3100, 2770, 2780],
      [1100, 1080, 270, 2410, 1930],
      [980, 1240, 3080, 160, 3990, 2380, 1680],
      [120, 290, 160, 140, 110, 190, 10, 230, 370, 310, 350, 280, 240, 150, 100, 250, 80, 380, 30,
        20, 330, 50, 300, 60, 390, 180, 270, 90, 210, 260, 170, 200, 320, 220, 340],
      [360, 180, 60, 70, 140, 220, 190, 250, 280, 100, 240, 90, 10, 150, 340, 290, 130, 370, 310,
        50, 200, 270, 170, 420, 410, 300, 320, 260, 380, 230, 20, 400, 40, 110, 160, 210, 330,
        390]]
  avlTrees ++ sequences.map grow ++
    [.node (.node .leaf 10 0 .leaf) 20 1
        (.node (.node .leaf 25 0 .leaf) 30 7 (.node .leaf 40 0 .leaf)),
      .node (.node .leaf 3 0 .leaf) 4 7 (.node .leaf 5 0 .leaf),
      .node (.node .leaf 1 0 .leaf) 2 1 (.node .leaf 4 (0 - 1) (.node .leaf 5 0 .leaf)),
      .node (.node (.node .leaf 3 0 .leaf) 4 1 .leaf) 10 (0 - 1) (.node .leaf 12 0 .leaf),
      setFactors 1 (grow [40, 20, 60, 10, 30, 50, 70]),
      .node (.node .leaf 5 0 .leaf) 5 0 (.node .leaf 5 0 .leaf)]

/-- The pairs of a key and a tree of the cases: each tree of `deleteTrees` with each of its
`deleteProbes`. -/
def deleteInputs : List (UInt64 × AvlTree) :=
  deleteTrees.flatMap fun t => (deleteProbes t).map (·, t)

end Library.Trees.AvlDelete
