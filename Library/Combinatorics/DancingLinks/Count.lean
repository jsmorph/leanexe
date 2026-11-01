import Library.Combinatorics.DancingLinks.Spec
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! The count of exact covers of a set of items, and the recursion of Algorithm X.  `coversOf os B`
is the number of sets of indices of the options of `os` that lie inside `B` and contain each item
of `B` in exactly one chosen option.  `coversOf_empty` gives 1 for no items, and `coversOf_rec`
gives, for any item `i` of `B`, the sum over the options inside `B` that contain `i` of the counts
of `B` without that option's items: each cover holds exactly one option through `i`, and removing
it leaves a cover of the rest.  `refCovers` computes the count by that recursion on lists, and
`refCount_eq` shows that `refCount` equals `coverCount` on valid inputs, and `countRef_eq` that
`countRef` equals `countSpec`, so the cases can compute their expected values without the
specification's sum over all sets of options. -/

namespace Library.Combinatorics.DancingLinks

open Finset

/-- Option `k` of `os` lies inside `B`. -/
def Inside (os : List (List Nat)) (B : Finset Nat) (k : Nat) : Prop := ∀ j ∈ os[k]!, j ∈ B

instance (os : List (List Nat)) (B : Finset Nat) : DecidablePred (Inside os B) := fun k => by
  unfold Inside; infer_instance

/-- The indices of the options of `os` that lie inside `B`. -/
def insideOf (os : List (List Nat)) (B : Finset Nat) : Finset Nat :=
  (range os.length).filter (Inside os B)

/-- `S` holds, for each item of `B`, exactly one option that contains the item. -/
def Covers (os : List (List Nat)) (B S : Finset Nat) : Prop :=
  ∀ i ∈ B, (S.filter fun k => i ∈ os[k]!).card = 1

instance (os : List (List Nat)) (B : Finset Nat) : DecidablePred (Covers os B) := fun S => by
  unfold Covers; infer_instance

/-- The number of exact covers of `B` by the options of `os` inside `B`. -/
def coversOf (os : List (List Nat)) (B : Finset Nat) : Nat :=
  ((insideOf os B).powerset.filter (Covers os B)).card

/-- Every option of `os` holds an item. -/
def Nonempty' (os : List (List Nat)) : Prop := ∀ k < os.length, os[k]! ≠ []

theorem coversOf_empty (os : List (List Nat)) (hne : Nonempty' os) : coversOf os ∅ = 1 := by
  have hin : insideOf os ∅ = ∅ := by
    ext k
    simp only [insideOf, Inside, mem_filter, mem_range, Finset.notMem_empty, iff_false, not_and]
    intro hk hall
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ (hne k hk)
    exact hall j hj
  unfold coversOf
  rw [hin, powerset_empty]
  have : ({∅} : Finset (Finset Nat)).filter (Covers os ∅) = {∅} := by
    ext S
    simp only [mem_filter, mem_singleton, and_iff_left_iff_imp]
    intro _ i hi
    exact absurd hi (Finset.notMem_empty i)
  rw [this, card_singleton]

/-- Two options of a cover of `B` that share an item of `B` are one option. -/
theorem Covers.unique {os : List (List Nat)} {B S : Finset Nat} (h : Covers os B S) {i k k' : Nat}
    (hi : i ∈ B) (hk : k ∈ S) (hk' : k' ∈ S) (hik : i ∈ os[k]!) (hik' : i ∈ os[k']!) : k = k' := by
  have hc := h i hi
  rw [card_eq_one] at hc
  obtain ⟨a, ha⟩ := hc
  have h1 : k ∈ S.filter fun k => i ∈ os[k]! := mem_filter.mpr ⟨hk, hik⟩
  have h2 : k' ∈ S.filter fun k => i ∈ os[k]! := mem_filter.mpr ⟨hk', hik'⟩
  rw [ha, mem_singleton] at h1 h2
  rw [h1, h2]

/-- The covers of `B` that hold the option `k` through `i` correspond to the covers of `B` without
the items of option `k`, by removing `k`. -/
theorem card_covers_with (os : List (List Nat)) (hne : Nonempty' os) (B : Finset Nat) (i k : Nat)
    (hk : k ∈ (insideOf os B).filter fun k => i ∈ os[k]!) :
    (((insideOf os B).powerset.filter (Covers os B)).filter (k ∈ ·)).card =
      coversOf os (B \ os[k]!.toFinset) := by
  obtain ⟨hkB, hik⟩ := mem_filter.mp hk
  have hklen : k < os.length := (mem_range.mp (mem_filter.mp hkB).1)
  have hkin : Inside os B k := (mem_filter.mp hkB).2
  set o := os[k]!.toFinset with ho
  unfold coversOf
  refine card_nbij' (fun S => S.erase k) (fun S => insert k S) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_coe, mem_filter, mem_powerset] at hS ⊢
    obtain ⟨⟨hsub, hcov⟩, hkS⟩ := hS
    refine ⟨?_, ?_⟩
    · intro k' hk'
      obtain ⟨hne', hk'S⟩ := mem_erase.mp hk'
      have hk'in := mem_filter.mp (hsub hk'S)
      refine mem_filter.mpr ⟨hk'in.1, ?_⟩
      intro j hj
      have hjB : j ∈ B := hk'in.2 j hj
      refine mem_sdiff.mpr ⟨hjB, ?_⟩
      intro hjo
      rw [ho, List.mem_toFinset] at hjo
      exact hne' (hcov.unique hjB hk'S hkS hj hjo)
    · intro i' hi'
      obtain ⟨hi'B, hi'o⟩ := mem_sdiff.mp hi'
      have : ((S.erase k).filter fun k => i' ∈ os[k]!) = S.filter fun k => i' ∈ os[k]! := by
        ext k'
        simp only [mem_filter, mem_erase]
        constructor
        · exact fun h => ⟨h.1.2, h.2⟩
        · intro h
          refine ⟨⟨?_, h.1⟩, h.2⟩
          rintro rfl
          exact hi'o (by rw [ho, List.mem_toFinset]; exact h.2)
      rw [this]
      exact hcov i' hi'B
  · intro S' hS'
    simp only [mem_coe, mem_filter, mem_powerset] at hS' ⊢
    obtain ⟨hsub, hcov⟩ := hS'
    have hS'B : ∀ k' ∈ S', Inside os B k' ∧ ∀ j ∈ os[k']!, j ∉ o := by
      intro k' hk'
      have h := (mem_filter.mp (hsub hk')).2
      exact ⟨fun j hj => (mem_sdiff.mp (h j hj)).1, fun j hj => (mem_sdiff.mp (h j hj)).2⟩
    refine ⟨⟨?_, ?_⟩, mem_insert_self k S'⟩
    · intro k' hk'
      rcases mem_insert.mp hk' with rfl | hk'
      · exact hkB
      · exact mem_filter.mpr ⟨(mem_filter.mp (hsub hk')).1, (hS'B k' hk').1⟩
    · intro i' hi'
      by_cases hio : i' ∈ o
      · have : ((insert k S').filter fun k => i' ∈ os[k]!) = {k} := by
          ext k'
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨rfl | hk', hik'⟩
            · rfl
            · exact absurd hio ((hS'B k' hk').2 i' hik')
          · rintro rfl
            exact ⟨Or.inl rfl, by rw [ho, List.mem_toFinset] at hio; exact hio⟩
        rw [this, card_singleton]
      · have : ((insert k S').filter fun k => i' ∈ os[k]!) = S'.filter fun k => i' ∈ os[k]! := by
          ext k'
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨rfl | hk', hik'⟩
            · exact absurd (by rw [ho, List.mem_toFinset]; exact hik') hio
            · exact ⟨hk', hik'⟩
          · exact fun h => ⟨Or.inr h.1, h.2⟩
        rw [this]
        exact hcov i' (mem_sdiff.mpr ⟨hi', hio⟩)
  · intro S hS
    exact insert_erase (mem_filter.mp (mem_coe.mp hS)).2
  · intro S' hS'
    simp only [mem_coe, mem_filter, mem_powerset] at hS'
    refine erase_insert ?_
    intro hkS'
    have h := (mem_filter.mp (hS'.1 hkS')).2
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ (hne k hklen)
    exact (mem_sdiff.mp (h j hj)).2 (by rw [ho, List.mem_toFinset]; exact hj)

/-- The recursion of Algorithm X: for any item `i` of `B`, the covers of `B` are the covers of `B`
without the items of an option through `i`, summed over those options. -/
theorem coversOf_rec (os : List (List Nat)) (hne : Nonempty' os) {B : Finset Nat} {i : Nat}
    (hi : i ∈ B) :
    coversOf os B = ∑ k ∈ (insideOf os B).filter (fun k => i ∈ os[k]!),
      coversOf os (B \ os[k]!.toFinset) := by
  set F := (insideOf os B).powerset.filter (Covers os B)
  set T := (insideOf os B).filter fun k => i ∈ os[k]!
  have hF : F = T.biUnion fun k => F.filter (k ∈ ·) := by
    ext S
    simp only [mem_biUnion, mem_filter]
    constructor
    · intro hS
      have hc := (mem_filter.mp hS).2 i hi
      obtain ⟨k, hk⟩ := card_pos.mp (by rw [hc]; exact Nat.one_pos)
      obtain ⟨hkS, hik⟩ := mem_filter.mp hk
      have hsub := mem_powerset.mp (mem_filter.mp hS).1
      exact ⟨k, mem_filter.mpr ⟨hsub hkS, hik⟩, hS, hkS⟩
    · rintro ⟨_, _, hS, _⟩
      exact hS
  have hdisj : (T : Set Nat).PairwiseDisjoint fun k => F.filter (k ∈ ·) := by
    intro k hk k' hk' hne'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨hSF, hkS⟩ := mem_filter.mp hS
    obtain ⟨_, hk'S⟩ := mem_filter.mp hS'
    exact hne' ((mem_filter.mp hSF).2.unique hi hkS hk'S (mem_filter.mp hk).2 (mem_filter.mp hk').2)
  unfold coversOf
  rw [show ((insideOf os B).powerset.filter (Covers os B)) = F from rfl, hF, card_biUnion hdisj]
  exact sum_congr rfl fun k hk => card_covers_with os hne B i k hk

/-- The count by the recursion of Algorithm X on lists: the active items `B`, the indices `avail`
of the options inside them, and the first active item as the item to cover. -/
def refCovers (os : List (List Nat)) : Nat → List Nat → List Nat → Nat
  | 0, _, _ => 0
  | _ + 1, [], _ => 1
  | f + 1, i :: rest, avail =>
    ((avail.filter fun k => i ∈ os[k]!).map fun k =>
      refCovers os f ((i :: rest).filter (· ∉ os[k]!))
        (avail.filter fun k' => os[k']!.all (· ∉ os[k]!))).sum

theorem refCovers_eq (os : List (List Nat)) (hne : Nonempty' os) :
    ∀ (f : Nat) (B avail : List Nat), B.Nodup → avail.Nodup → B.length < f →
      (∀ k, k ∈ avail ↔ k ∈ insideOf os B.toFinset) →
      refCovers os f B avail = coversOf os B.toFinset := by
  intro f
  induction f with
  | zero => intro B avail _ _ hf; omega
  | succ f ih =>
    intro B avail hB havail hf hav
    cases B with
    | nil =>
      rw [refCovers, List.toFinset_nil, coversOf_empty os hne]
    | cons i rest =>
      rw [refCovers, coversOf_rec os hne (i := i) (by simp)]
      have hnd : (avail.filter fun k => i ∈ os[k]!).Nodup := havail.filter _
      have hset : (avail.filter fun k => i ∈ os[k]!).toFinset =
          (insideOf os (i :: rest).toFinset).filter fun k => i ∈ os[k]! := by
        ext k
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_filter, hav]
      rw [← hset, List.sum_toFinset _ hnd]
      congr 1
      refine List.map_congr_left fun k hk => ?_
      obtain ⟨hka, hik⟩ := List.mem_filter.mp hk
      have hik' : i ∈ os[k]! := of_decide_eq_true hik
      have hrest : ((i :: rest).filter (· ∉ os[k]!)).toFinset =
          (i :: rest).toFinset \ os[k]!.toFinset := by
        ext j
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_sdiff]
      rw [← hrest]
      refine ih _ _ (hB.filter _) (havail.filter _) ?_ ?_
      · have hlt : ((i :: rest).filter (· ∉ os[k]!)).length < (i :: rest).length := by
          apply List.length_filter_lt_length_iff_exists.mpr
          exact ⟨i, List.mem_cons_self, by simpa using hik'⟩
        omega
      · intro k'
        rw [hrest]
        simp only [List.mem_filter, List.all_eq_true, decide_eq_true_eq, hav, insideOf, Inside,
          mem_filter, mem_range, mem_sdiff, List.mem_toFinset]
        constructor
        · rintro ⟨⟨hk'l, hk'B⟩, hdis⟩
          exact ⟨hk'l, fun j hj => ⟨hk'B j hj, hdis j hj⟩⟩
        · rintro ⟨hk'l, h⟩
          exact ⟨⟨hk'l, fun j hj => (h j hj).1⟩, fun j hj => (h j hj).2⟩

/-- No run that `List.splitOn a` cuts holds `a`. -/
theorem notMem_splitOn (a : Nat) :
    ∀ (xs : List Nat), ∀ l ∈ xs.splitOn a, a ∉ l := by
  intro xs
  rw [List.splitOn_eq_splitOnP]
  induction xs with
  | nil => simp [List.splitOnP_nil]
  | cons x xs ih =>
    intro l hl
    rw [List.splitOnP_cons_eq_ite_modifyHead] at hl
    split at hl
    · rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · exact ih l hl
    · rename_i hx
      have hxa : x ≠ a := by simpa using hx
      cases hs : xs.splitOnP (· == a) with
      | nil => exact absurd hs (List.splitOnP_ne_nil _ _)
      | cons h t =>
        rw [hs] at hl
        simp only [List.modifyHead_cons, List.mem_cons] at hl
        rcases hl with rfl | hl
        · simp only [List.mem_cons, not_or]
          exact ⟨fun e => hxa e.symm, ih h (by rw [hs]; exact List.mem_cons_self)⟩
        · exact ih l (by rw [hs]; exact List.mem_cons_of_mem _ hl)

/-- Every item of every option is nonzero, and no option is empty. -/
theorem options_items (x : Array UInt64) : ∀ o ∈ options x, o ≠ [] ∧ 0 ∉ o := by
  intro o ho
  unfold options at ho
  obtain ⟨hmem, hne⟩ := List.mem_filter.mp ho
  exact ⟨of_decide_eq_true hne, notMem_splitOn 0 _ o hmem⟩

theorem options_nonempty (x : Array UInt64) : Nonempty' (options x) := fun k hk => by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact (options_items x _ (List.getElem_mem hk)).1

/-- On a valid input, every option lies inside `1..N`, so the covers of the specification are
the covers of `1..N` by all options. -/
theorem coverCount_eq (x : Array UInt64) (hv : Valid x) :
    coverCount x = coversOf (options x) (Finset.Icc 1 (itemCount x)) := by
  unfold coverCount coversOf
  have hin : insideOf (options x) (Finset.Icc 1 (itemCount x)) = range (options x).length := by
    ext k
    simp only [insideOf, Inside, mem_filter, mem_range, and_iff_left_iff_imp, Finset.mem_Icc]
    intro hk j hj
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hj
    have hmem := List.getElem_mem hk
    have h0 := (options_items x _ hmem).2
    refine ⟨Nat.pos_of_ne_zero fun e => h0 (e ▸ hj), (hv.2 _ hmem).2 j hj⟩
  rw [hin]
  rfl

/-- The count of the cases: the recursion from all items `1..N` and all options. -/
def refCount (x : Array UInt64) : Nat :=
  refCovers (options x) (itemCount x + 1) (List.range' 1 (itemCount x))
    (List.range (options x).length)

theorem refCount_eq (x : Array UInt64) (hv : Valid x) : refCount x = coverCount x := by
  rw [coverCount_eq x hv, refCount]
  have hset : (List.range' 1 (itemCount x)).toFinset = Finset.Icc 1 (itemCount x) := by
    ext j
    simp only [List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
    omega
  rw [← hset]
  refine refCovers_eq _ (options_nonempty x) _ _ _ (List.nodup_range' ..) List.nodup_range
    (by simp) ?_
  intro k
  rw [hset]
  have hin : insideOf (options x) (Finset.Icc 1 (itemCount x)) = range (options x).length := by
    ext k
    simp only [insideOf, Inside, mem_filter, mem_range, and_iff_left_iff_imp, Finset.mem_Icc]
    intro hk j hj
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hj
    have hmem := List.getElem_mem hk
    have h0 := (options_items x _ hmem).2
    refine ⟨Nat.pos_of_ne_zero fun e => h0 (e ▸ hj), (hv.2 _ hmem).2 j hj⟩
  rw [hin, List.mem_range, mem_range]

/-- `countSpec` with `refCount` in place of the sum over all sets of options. -/
def countRef (x : Array UInt64) : UInt64 := UInt64.ofNat (refCount x)

theorem countRef_eq (x : Array UInt64) (hv : Valid x) : countRef x = countSpec x := by
  rw [countRef, countSpec, refCount_eq x hv]

end Library.Combinatorics.DancingLinks
