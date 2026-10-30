import Examples.TreeLookup.Program
import Examples.TreeLookup.Spec
import LeanExe.IR.Combinators

/-! The program equals the specification, a fact about the Lean definitions that the theorems of
both compilers use. -/

namespace Examples.TreeLookup

theorem search_inner (input : Array UInt64) (query : UInt64) {j : Nat} (hj : j < 3) :
    search input query j =
      if query = input[2 * j + 1]! then #[input[2 * j + 2]!, 1]
      else if query < input[2 * j + 1]! then search input query (2 * j + 1)
      else search input query (2 * j + 2) := by
  rw [search]
  simp [show ¬3 ≤ j by omega]

theorem search_leaf (input : Array UInt64) (query : UInt64) {j : Nat} (hj : 3 ≤ j) :
    search input query j =
      if query = input[2 * j + 1]! then #[input[2 * j + 2]!, 1] else #[0, 0] := by
  rw [search]
  simp [hj]

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  dsimp only
  by_cases hs : xs.size = 15
  · simp only [hs, ite_true, LeanExe.loop, search_inner xs _ (j := 0) (by decide),
      search_inner xs _ (j := 1) (by decide), search_inner xs _ (j := 2) (by decide),
      search_leaf xs _ (j := 3) (by decide), search_leaf xs _ (j := 4) (by decide),
      search_leaf xs _ (j := 5) (by decide), search_leaf xs _ (j := 6) (by decide)]
    simp
    generalize xs[0]! = q
    by_cases h0 : q = xs[1]!
    · subst h0; simp
    by_cases l0 : q < xs[1]!
    · by_cases h1 : q = xs[3]!
      · subst h1; simp [h0, l0]
      by_cases l1 : q < xs[3]!
      · by_cases h3 : q = xs[7]!
        · subst h3; simp [h0, l0, h1, l1]
        · simp [h0, l0, h1, l1, h3]
      · by_cases h4 : q = xs[9]!
        · subst h4; simp [h0, l0, h1, l1]
        · simp [h0, l0, h1, l1, h4]
    · by_cases h2 : q = xs[5]!
      · subst h2; simp [h0, l0]
      by_cases l2 : q < xs[5]!
      · by_cases h5 : q = xs[11]!
        · subst h5; simp [h0, l0, h2, l2]
        · simp [h0, l0, h2, l2, h5]
      · by_cases h6 : q = xs[13]!
        · subst h6; simp [h0, l0, h2, l2]
        · simp [h0, l0, h2, l2, h6]
  · have hok : (xs.size.toUInt64 == 15) = false := by
      rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, hn]; exact hs
    simp [hok, hs]

end Examples.TreeLookup
