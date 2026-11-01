import Library.Combinatorics.DancingLinks.Read
import Library.Combinatorics.DancingLinks.Hide
import LeanExe.Dialect.Lemmas

/-! The layout of an input.  `layout x` holds the number of items and the options of `x`.  Node
`first k` begins option `k`, so `first_eq` writes it as `N + 2` plus one node for each item and
one spacer for each option before `k`.  `nodeCount` counts, word by word, one node for each nonzero
word and one spacer at the first word of each run, and `nodeCount_eq` shows that the count is the
sum over the options, from the reader of `Read.lean`, so the item links begin at
`3 (N + 2 + nodeCount x) = base`.  `layout_good`, in `BuildInit.lean`, gives the conditions of
`Layout.Good` for a valid input of fewer than `2^50` words. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- The layout of an input: its number of items and its options. -/
def layout (x : Array UInt64) : Layout := ⟨itemCount x, options x⟩

/-- The number of nodes and spacers of the options of a list, one more than the number of items of
each. -/
def runCount (os : List (List Nat)) : Nat := (os.map fun o => o.length + 1).sum

theorem first_eq (L : Layout) : ∀ k, k ≤ L.os.length →
    L.first k = L.n + 2 + runCount (L.os.take k)
  | 0, _ => by simp [Layout.first, runCount]
  | k + 1, hk => by
    rw [Layout.first, first_eq L k (by omega), List.take_add_one,
      List.getElem?_eq_getElem (by omega), Option.toList_some]
    simp only [runCount, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Layout.len]
    rw [getElem!_pos L.os k (by omega)]
    omega

/-- The words of the input after the first, as natural numbers. -/
def words (x : Array UInt64) : List Nat := (x.toList.drop 1).map UInt64.toNat

theorem words_length (x : Array UInt64) : (words x).length = x.size - 1 := by
  simp [words]

theorem words_get (x : Array UInt64) {k : Nat} (hk : 1 ≤ k) (hk' : k < x.size) :
    (words x)[k - 1]'(by rw [words_length]; omega) = (x[k]!).toNat := by
  simp only [words, List.getElem_map, List.getElem_drop]
  rw [getElem!_pos x k hk', ← Array.getElem_toList]
  congr 2
  omega

/-- The count of nodes and spacers after a prefix of the words, as the reader's state gives it. -/
def readCount (s : List (List Nat) × List Nat) : Nat :=
  runCount s.1 + (if s.2 = [] then 0 else s.2.length + 1)

theorem readCount_step (s : List (List Nat) × List Nat) (w : Nat) :
    readCount (readStep s w) =
      readCount s + (if w = 0 then 0 else if s.2 = [] then 2 else 1) := by
  unfold readStep readCount
  by_cases hw : w = 0
  · rw [ite_eq_left hw, ite_eq_left hw]
    split
    · simp
    · rename_i h
      simp [h, runCount, List.map_append, List.sum_append]
  · rw [ite_eq_right hw, ite_eq_right hw]
    by_cases h : s.2 = []
    · simp [h]
    · simp [h]; omega

/-- The run being read is empty at the start and after a zero. -/
theorem read_cur_nil (pre : List Nat) (w : Nat) :
    ((pre ++ [w]).foldl readStep ([], [])).2 = [] ↔ w = 0 := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold readStep
  by_cases hw : w = 0
  · rw [ite_eq_left hw]; split <;> simp [*]
  · rw [ite_eq_right hw]; simp [hw]

theorem readCount_finish (s : List (List Nat) × List Nat) : readCount s = runCount (finish s) := by
  unfold readCount finish
  split <;> simp [runCount, List.map_append, List.sum_append]

theorem nodeCount_eq (x : Array UInt64) (hx : x.size < 2 ^ 62) :
    (nodeCount x).toNat = runCount (options x) := by
  have hsz : x.size.toUInt64.toNat = x.size := size_toUInt64 x (by omega)
  let F : UInt64 → UInt64 → UInt64 := fun k s =>
    if k = 0 ∨ x[k.toNat]! = 0 then s
      else if k = 1 ∨ x[(k - 1).toNat]! = 0 then s + 2 else s + 1
  show (LeanExe.loop x.size.toUInt64 (0 : UInt64) F).toNat = _
  have key := loop_induction (n := x.size.toUInt64) (init := (0 : UInt64))
    (f := F) (fun k s => s.toNat = readCount (((words x).take (k - 1)).foldl readStep ([], [])) ∧
      s.toNat ≤ 2 * k) (by simp [readCount, runCount]) ?_
  · rw [hsz] at key
    rw [key.1, readCount_finish, show x.size - 1 = (words x).length by rw [words_length],
      List.take_length, finish_read (words x) [] [] (by simp), List.nil_append, List.nil_append]
    rfl
  · intro k s hk ⟨hs1, hs2⟩
    rw [hsz] at hk
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
    show (F (UInt64.ofNat k) s).toNat = _ ∧ (F (UInt64.ofNat k) s).toNat ≤ _
    simp only [F]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [show UInt64.ofNat 0 = 0 from rfl, ite_eq_left (Or.inl rfl)]
      exact ⟨hs1, by simp at hs2 ⊢; omega⟩
    have hk0' : UInt64.ofNat k ≠ 0 := fun e => by rw [e] at hk64; simp at hk64; omega
    have hw := words_get x (k := k) (by omega) hk
    have htake : (words x).take (k + 1 - 1) =
        (words x).take (k - 1) ++ [(words x)[k - 1]'(by rw [words_length]; omega)] := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, List.take_add_one,
        List.getElem?_eq_getElem (by rw [words_length]; omega), Option.toList_some]
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, readCount_step, ← hs1, hw,
      hk64]
    have hcur : (((words x).take (k - 1)).foldl readStep ([], [])).2 = [] ↔
        (UInt64.ofNat k = 1 ∨ x[(UInt64.ofNat k - 1).toNat]! = 0) := by
      have hsub : (UInt64.ofNat k - 1).toNat = k - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp [hk64]
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        subst this
        simp
      · have hk1 : UInt64.ofNat k ≠ 1 := fun e => by rw [e] at hk64; simp at hk64; omega
        have htake' : (words x).take (k - 1) =
            (words x).take (k - 2) ++ [(words x)[k - 2]'(by rw [words_length]; omega)] := by
          rw [show k - 1 = (k - 2) + 1 by omega, List.take_add_one,
            List.getElem?_eq_getElem (by rw [words_length]; omega), Option.toList_some]
        have hw2 : (words x)[k - 2]'(by rw [words_length]; omega) = (x[k - 1]!).toNat := by
          have := words_get x (k := k - 1) (by omega) (by omega)
          simp only [show k - 1 - 1 = k - 2 by omega] at this
          exact this
        rw [htake', read_cur_nil, hsub, hw2]
        constructor
        · intro h; exact Or.inr (UInt64.toNat_inj.mp (by rw [h]; rfl))
        · rintro (h | h)
          · exact absurd h hk1
          · rw [h]; rfl
    by_cases hw0 : (x[k]!).toNat = 0
    · have : UInt64.ofNat k = 0 ∨ x[k]! = 0 := Or.inr (UInt64.toNat_inj.mp (by rw [hw0]; rfl))
      rw [ite_eq_left this, ite_eq_left hw0]
      exact ⟨rfl, by omega⟩
    · have hnz : ¬ (UInt64.ofNat k = 0 ∨ x[k]! = 0) := by
        rintro (h | h)
        · exact hk0' h
        · exact hw0 (by rw [h]; rfl)
      rw [ite_eq_right hnz, ite_eq_right hw0]
      by_cases hc : (((words x).take (k - 1)).foldl readStep ([], [])).2 = []
      · rw [ite_eq_left (hcur.mp hc), ite_eq_left hc]
        refine ⟨?_, ?_⟩ <;> simp only [UInt64.toNat_add, UInt64.reduceToNat] <;> omega
      · rw [ite_eq_right (fun h => hc (hcur.mpr h)), ite_eq_right hc]
        refine ⟨?_, ?_⟩ <;> simp only [UInt64.toNat_add, UInt64.reduceToNat] <;> omega

end Library.Combinatorics.DancingLinks
