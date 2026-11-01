import Library.Combinatorics.DancingLinks.Search
import Library.Combinatorics.DancingLinks.ValidProof

/-! The program equals the specification.  `count_eq` composes the parts of the proof: the item
links begin at `3 (N + 2 + nodeCount x) = base` by `nodeCount_eq` and `first_eq`, step X1 leaves
the invariant of the search for all items by `build_inv`, the search counts the exact covers by
`search_eq`, and `coverCount_eq` gives the specification's count the same form.  `valid_eq`, in
`ValidProof.lean`, shows that `valid` decides `Valid`.  Both hold for inputs of fewer than `2^50`
words, which every array in memory satisfies. -/

namespace Library.Combinatorics.DancingLinks

open Finset

/-- On a valid input, `count` is the number of exact covers modulo `2^64`. -/
theorem count_eq (x : Array UInt64) (hv : Valid x) (hx : x.size < 2 ^ 50) :
    count x = countSpec x := by
  have hL : (layout x).Good := layout_good x hv hx
  have hn : (x[(0 : UInt64).toNat]!).toNat = itemCount x := first_word x
  have hnc : (nodeCount x).toNat = runCount (options x) := nodeCount_eq x (by omega)
  have hrc := runCount_options_le x
  have hN := hv.1
  have hb : (3 * (x[(0 : UInt64).toNat]! + 2 + nodeCount x)).toNat = (layout x).base := by
    unfold Layout.base
    rw [first_eq _ _ le_rfl, List.take_length]
    have hn' : (x[0]!).toNat = itemCount x := hn
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat, hnc]
    rw [hn']
    show 3 * (((itemCount x + 2) % 2 ^ 64 + runCount (options x)) % 2 ^ 64) % 2 ^ 64 =
      3 * (itemCount x + 2 + runCount (options x))
    omega
  unfold count
  dsimp only
  rw [search_eq hL hb (itemCount x) _ _ _ hn (build_inv x hv hx hb) (by simp; rfl)]
  rw [countSpec, coverCount_eq x hv]
  rfl

end Library.Combinatorics.DancingLinks
