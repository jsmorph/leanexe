import TestSupport.Modules.UnionFind

/-! The inputs of the verified compiler's cases of equivalence classes with path compression and
union by size. -/

namespace Library.Graphs.WeightedUnionFind

/-- The pairs that merge the trees of `n` elements in `levels` rounds: in round `l`, the element
`b·2^(l+1)` with `b·2^(l+1) + 2^l`, whose trees are equal in size, so that union by size builds
binomial trees and the element with every low bit set lies `levels` links below its root. -/
def binomial (n levels : Nat) : List (UInt64 × UInt64) :=
  (List.range levels).flatMap fun l =>
    (List.range (n / 2 ^ (l + 1))).map fun b =>
      (UInt64.ofNat (b * 2 ^ (l + 1)), UInt64.ofNat (b * 2 ^ (l + 1) + 2 ^ l))

/-- The inputs of the cases: those of Algorithm E, `classInputs`, whose pairs `(i, i + 1)` build a
tree of depth 1 under union by size, and inputs whose searches are long.  A pair `(31, 31)` after
the binomial tree of 32 elements searches 5 links and compresses them, a pair `(15, 31)` joins two
binomial trees of 16 elements through two paths of 4 links, and the same holds for 4,096 elements
with paths of 12 and 11 links.  The input `(4, [1, 2, 0, 3], [0, 3, 2, 2])` compresses a path in a
small forest. -/
def weightedInputs : List (Nat × List UInt64 × List UInt64) :=
  let case := fun (n : Nat) (ps : List (UInt64 × UInt64)) =>
    (n, ps.map (·.1), ps.map (·.2))
  Library.Graphs.UnionFind.classInputs ++
    [(4, [1, 2, 0, 3], [0, 3, 2, 2]),
      case 32 (binomial 32 5 ++ [(31, 31)]),
      case 32 (binomial 32 4 ++ [(15, 31), (31, 31)]),
      case 4096 (binomial 4096 12 ++ [(4095, 4095)]),
      case 4096 (binomial 4096 11 ++ [(2047, 4095), (4095, 4095), (0, 4095)])]

end Library.Graphs.WeightedUnionFind
