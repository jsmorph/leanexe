import Library.Trees.Search.Program
import Library.Trees.Search.Spec

/-! The proofs that `search` and `insert` compute `algorithmT` and that `algorithmT` meets
`SearchTree` on every binary search tree.  For the library's `KeyTree.insert`, which computes the
tree of `algorithmT` by recursion, they prove that equality and the membership and ordering
theorems.  `descend_eq` states the link reversal: `descend x path t` returns what `ascend` returns
from the tree of `algorithmT x t` below the same `path`. -/

namespace Library.Trees.Search

open Library.Trees.WordTree

theorem search_eq (x : UInt64) (t : KeyTree) : search x t = (algorithmT x t).1 := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr =>
    by_cases h : x < k
    · simp [search, algorithmT, h, ihl]
    · by_cases h' : k < x <;> simp [search, algorithmT, h, h', ihr]

theorem descend_eq (x : UInt64) (path t : KeyTree) :
    descend x path t = ascend x path (algorithmT x t).2 := by
  induction t generalizing path with
  | leaf => simp [descend, algorithmT]
  | node l k r ihl ihr =>
    by_cases h : x < k
    · simp [descend, algorithmT, h, ihl, ascend]
    · by_cases h' : k < x
      · simp [descend, algorithmT, h, h', ihr, ascend]
      · simp [descend, algorithmT, h, h']

theorem insert_eq (x : UInt64) (t : KeyTree) : insert x t = (algorithmT x t).2 := by
  simp [insert, descend_eq, ascend]

theorem algorithmT_snd (x : UInt64) (t : KeyTree) : (algorithmT x t).2 = t.insert x := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr =>
    by_cases h : x < k
    · simp [algorithmT, KeyTree.insert, h, ihl]
    · by_cases h' : k < x <;> simp [algorithmT, KeyTree.insert, h, h', ihr]

theorem eq_of_not_lt {x k : UInt64} (h : ¬x < k) (h' : ¬k < x) : x = k :=
  UInt64.le_antisymm (UInt64.not_lt.mp h') (UInt64.not_lt.mp h)

/-- Algorithm T adds `x` to the keys of any tree. -/
theorem mem_keys_algorithmT (x y : UInt64) (t : KeyTree) :
    y ∈ keys (algorithmT x t).2 ↔ y = x ∨ y ∈ keys t := by
  induction t with
  | leaf => simp [algorithmT, keys]
  | node l k r ihl ihr =>
    by_cases h : x < k
    · simp only [algorithmT, h, ↓reduceIte, keys, List.mem_append, List.mem_cons, ihl]
      tauto
    · by_cases h' : k < x
      · simp only [algorithmT, h, h', ↓reduceIte, keys, List.mem_append, List.mem_cons, ihr]
        tauto
      · have := eq_of_not_lt h h'
        subst this
        simp only [algorithmT, h, ↓reduceIte, keys, List.mem_append, List.mem_cons]
        tauto

theorem ordered_node {l r : KeyTree} {k : UInt64} :
    Ordered (.node l k r) ↔
      Ordered l ∧ Ordered r ∧ (∀ a ∈ keys l, a < k) ∧ (∀ b ∈ keys r, k < b) := by
  simp only [Ordered, keys, List.pairwise_append, List.pairwise_cons, List.mem_cons]
  constructor
  · rintro ⟨hl, ⟨hk, hr⟩, hlr⟩
    exact ⟨hl, hr, fun a ha => hlr a ha k (.inl rfl), hk⟩
  · rintro ⟨hl, hr, hlk, hkr⟩
    refine ⟨hl, ⟨hkr, hr⟩, fun a ha b hb => ?_⟩
    rcases hb with rfl | hb
    · exact hlk a ha
    · exact UInt64.lt_trans (hlk a ha) (hkr b hb)

theorem found_algorithmT (x : UInt64) (t : KeyTree) (ht : Ordered t) :
    (algorithmT x t).1 = true ↔ x ∈ keys t := by
  induction t with
  | leaf => simp [algorithmT, keys]
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hlk, hkr⟩ := ordered_node.mp ht
    by_cases h : x < k
    · simp only [algorithmT, h, ↓reduceIte, ihl hl, keys, List.mem_append, List.mem_cons]
      constructor
      · exact .inl
      · rintro (hx | rfl | hx)
        · exact hx
        · exact absurd h (UInt64.lt_irrefl _)
        · exact absurd (UInt64.lt_trans h (hkr x hx)) (UInt64.lt_irrefl _)
    · by_cases h' : k < x
      · simp only [algorithmT, h, h', ↓reduceIte, ihr hr, keys, List.mem_append,
          List.mem_cons]
        constructor
        · exact fun hx => .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact absurd (UInt64.lt_trans h' (hlk x hx)) (UInt64.lt_irrefl _)
          · exact absurd h' (UInt64.lt_irrefl _)
          · exact hx
      · have := eq_of_not_lt h h'
        subst this
        simp [algorithmT, keys, h]

theorem ordered_algorithmT (x : UInt64) (t : KeyTree) (ht : Ordered t) :
    Ordered (algorithmT x t).2 := by
  induction t with
  | leaf => simp [algorithmT, Ordered, keys]
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hlk, hkr⟩ := ordered_node.mp ht
    by_cases h : x < k
    · simp only [algorithmT, h, ↓reduceIte]
      refine ordered_node.mpr ⟨ihl hl, hr, fun a ha => ?_, hkr⟩
      rcases (mem_keys_algorithmT x a l).mp ha with rfl | ha
      · exact h
      · exact hlk a ha
    · by_cases h' : k < x
      · simp only [algorithmT, h, h', ↓reduceIte]
        refine ordered_node.mpr ⟨hl, ihr hr, hlk, fun b hb => ?_⟩
        rcases (mem_keys_algorithmT x b r).mp hb with rfl | hb
        · exact h'
        · exact hkr b hb
      · simpa [algorithmT, h, h'] using ht

theorem orderedInsert_append_cons (x k : UInt64) (hx : x ≤ k) (as bs : List UInt64) :
    (as ++ k :: bs).orderedInsert (· ≤ ·) x = as.orderedInsert (· ≤ ·) x ++ k :: bs := by
  induction as with
  | nil => simp [hx]
  | cons a as ih => by_cases h : x ≤ a <;> simp [h, ih]

theorem orderedInsert_append_of_lt (x : UInt64) (as bs : List UInt64) (hx : ∀ a ∈ as, a < x) :
    (as ++ bs).orderedInsert (· ≤ ·) x = as ++ bs.orderedInsert (· ≤ ·) x := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have h : ¬x ≤ a := UInt64.not_le.mpr (hx a (.head _))
    simp [h, ih fun b hb => hx b (.tail _ hb)]

theorem keys_algorithmT (x : UInt64) (t : KeyTree) (ht : Ordered t) :
    keys (algorithmT x t).2 =
      if x ∈ keys t then keys t else (keys t).orderedInsert (· ≤ ·) x := by
  induction t with
  | leaf => simp [algorithmT, keys]
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hlk, hkr⟩ := ordered_node.mp ht
    by_cases h : x < k
    · have hmem : x ∈ keys (.node l k r) ↔ x ∈ keys l := by
        rw [← found_algorithmT x _ ht, ← found_algorithmT x l hl]
        simp [algorithmT, h]
      simp only [hmem]
      simp only [algorithmT, h, ↓reduceIte, keys, ihl hl]
      by_cases hx : x ∈ keys l
      · simp [hx]
      · simp [hx, orderedInsert_append_cons x k (UInt64.le_of_lt h)]
    · by_cases h' : k < x
      · have hmem : x ∈ keys (.node l k r) ↔ x ∈ keys r := by
          rw [← found_algorithmT x _ ht, ← found_algorithmT x r hr]
          simp [algorithmT, h, h']
        have hlt : ∀ a ∈ keys l ++ [k], a < x := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact UInt64.lt_trans (hlk a ha) h'
          · rw [List.mem_singleton.mp ha]
            exact h'
        have hins := orderedInsert_append_of_lt x (keys l ++ [k]) (keys r) hlt
        simp only [List.append_assoc, List.singleton_append] at hins
        simp only [hmem]
        simp only [algorithmT, h, h', ↓reduceIte, keys, ihr hr]
        by_cases hx : x ∈ keys r
        · simp [hx]
        · simp [hx, hins]
      · have := eq_of_not_lt h h'
        subst this
        simp [algorithmT, keys, h]

/-- Algorithm T on a binary search tree meets the guarantees of `SearchTree`. -/
theorem searchTree (x : UInt64) (t : KeyTree) (ht : Ordered t) : SearchTree x t :=
  ⟨found_algorithmT x t ht, ordered_algorithmT x t ht, keys_algorithmT x t ht⟩

/-- The library's insertion adds `x` to the keys of any tree. -/
theorem mem_keys_insert (x y : UInt64) (t : KeyTree) :
    y ∈ keys (t.insert x) ↔ y = x ∨ y ∈ keys t := by
  rw [← algorithmT_snd]
  exact mem_keys_algorithmT x y t

/-- The library's insertion keeps a binary search tree ordered. -/
theorem ordered_insert (x : UInt64) (t : KeyTree) (ht : Ordered t) : Ordered (t.insert x) := by
  rw [← algorithmT_snd]
  exact ordered_algorithmT x t ht

end Library.Trees.Search
