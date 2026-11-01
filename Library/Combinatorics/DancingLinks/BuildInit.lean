import Library.Combinatorics.DancingLinks.Layout

/-! The parts of step X1: the layout of a valid input satisfies `Layout.Good`, and the links of a
column after the insertion of a node above all of its nodes.  `layout_good` takes the bounds on the
items and the absence of repeats from `Valid`, and the nonempty options without zeros from
`options`.  The bound on the array's size follows from `N ≤ 998`, the bound on the input's size, and
`runCount_options_le`, which bounds the number of nodes and spacers by twice the number of words.
`nxt_insert_max` and `prv_insert_max` give the successor and predecessor in the column after the
insertion, which `col_append` of `Build.lean` uses for a node that step X1 adds at the bottom of a
column. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

theorem readCount_le : ∀ (ws : List Nat) (s : List (List Nat) × List Nat),
    readCount (ws.foldl readStep s) ≤ readCount s + 2 * ws.length
  | [], s => by simp
  | w :: ws, s => by
    rw [List.foldl_cons]
    have := readCount_le ws (readStep s w)
    rw [readCount_step] at this
    simp only [List.length_cons]
    split at this <;> (try split at this) <;> omega

theorem runCount_options_le (x : Array UInt64) : runCount (options x) ≤ 2 * x.size := by
  have h := readCount_le (words x) ([], [])
  rw [readCount_finish, finish_read (words x) [] [] (by simp), List.nil_append,
    List.nil_append, words_length] at h
  have : readCount (([] : List (List Nat)), ([] : List Nat)) = 0 := by simp [readCount, runCount]
  rw [this] at h
  exact le_trans h (by omega)

theorem layout_good (x : Array UInt64) (hv : Valid x) (hx : x.size < 2 ^ 50) :
    (layout x).Good := by
  have hget : ∀ k < (options x).length, (options x)[k]! ∈ options x := fun k hk => by
    rw [getElem!_pos (options x) k hk]; exact List.getElem_mem hk
  have hmem : ∀ k < (options x).length, ∀ m < ((options x)[k]!).length,
      (layout x).item k m ∈ (options x)[k]! := by
    intro k _ m hm
    unfold Layout.item
    show ((options x)[k]!)[m]! ∈ _
    rw [getElem!_pos ((options x)[k]!) m hm]
    exact List.getElem_mem _
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk m hm => ?_, ?_⟩
  · exact List.length_pos_of_ne_nil (options_items x _ (hget k hk)).1
  · exact (hv.2 _ (hget k hk)).1
  · have h := hmem k hk m hm
    have h0 := (options_items x _ (hget k hk)).2
    have hle := (hv.2 _ (hget k hk)).2 _ h
    exact ⟨Nat.pos_of_ne_zero fun e => h0 (e ▸ h), hle⟩
  · unfold Layout.base
    rw [first_eq _ _ le_rfl, List.take_length]
    have := runCount_options_le x
    have := hv.1
    simp only [layout] at *
    omega

/-- Inserting a node above every node of a column: the new node follows the old last one and
precedes the header. -/
theorem nxt_insert_max {c : Nat} {Q : Finset Nat} (hA : Above c Q) {p : Nat}
    (hp : ∀ y ∈ insert c Q, y < p) {y : Nat} (hy : y ∈ insert c Q) :
    nxt c (insert p Q) y = if nxt c Q y = c then p else nxt c Q y := by
  unfold nxt
  by_cases h : (Q.filter (y < ·)).Nonempty
  · have hne : ((insert p Q).filter (y < ·)).Nonempty := by
      obtain ⟨z, hz⟩ := h
      exact ⟨z, mem_filter.mpr ⟨mem_insert_of_mem (mem_filter.mp hz).1, (mem_filter.mp hz).2⟩⟩
    rw [dite_eq_left hne, dite_eq_left h]
    have hmQ := (mem_filter.mp (min'_mem _ h)).1
    have hc : (Q.filter (y < ·)).min' h ≠ c := Nat.ne_of_gt (hA _ hmQ)
    rw [ite_eq_right hc]
    apply le_antisymm
    · apply min'_le
      exact mem_filter.mpr ⟨mem_insert_of_mem hmQ, (mem_filter.mp (min'_mem _ h)).2⟩
    · apply le_min'
      intro z hz
      obtain ⟨hzQ, hyz⟩ := mem_filter.mp hz
      rcases mem_insert.mp hzQ with rfl | hzQ
      · exact Nat.le_of_lt (hp _ (mem_insert_of_mem hmQ))
      · exact min'_le _ _ (mem_filter.mpr ⟨hzQ, hyz⟩)
  · have hyp : y < p := hp y hy
    have hne : ((insert p Q).filter (y < ·)).Nonempty := ⟨p, mem_filter.mpr ⟨mem_insert_self _ _, hyp⟩⟩
    rw [dite_eq_left hne, dite_eq_right h, ite_eq_left rfl]
    apply le_antisymm
    · exact min'_le _ _ (mem_filter.mpr ⟨mem_insert_self _ _, hyp⟩)
    · apply le_min'
      intro z hz
      obtain ⟨hzQ, hyz⟩ := mem_filter.mp hz
      rcases mem_insert.mp hzQ with rfl | hzQ
      · exact le_rfl
      · exact absurd ⟨z, mem_filter.mpr ⟨hzQ, hyz⟩⟩ h

theorem nxt_insert_max_self {c : Nat} {Q : Finset Nat} {p : Nat} (hp : ∀ y ∈ insert c Q, y < p) :
    nxt c (insert p Q) p = c := by
  unfold nxt
  have : ¬ ((insert p Q).filter (p < ·)).Nonempty := by
    rintro ⟨z, hz⟩
    obtain ⟨hzQ, hpz⟩ := mem_filter.mp hz
    rcases mem_insert.mp hzQ with rfl | hzQ
    · omega
    · have := hp z (mem_insert_of_mem hzQ); omega
  rw [dite_eq_right this]

theorem prv_insert_max {c : Nat} {Q : Finset Nat} (hA : Above c Q) {p : Nat}
    (hp : ∀ y ∈ insert c Q, y < p) {y : Nat} (hy : y ∈ Q) : prv c (insert p Q) y = prv c Q y := by
  have hyc : y ≠ c := Nat.ne_of_gt (hA y hy)
  unfold prv
  rw [ite_eq_right hyc, ite_eq_right hyc]
  have hset : (insert p Q).filter (· < y) = Q.filter (· < y) := by
    ext z
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | hz, hzy⟩
      · have := hp y (mem_insert_of_mem hy); omega
      · exact ⟨hz, hzy⟩
    · exact fun h => ⟨Or.inr h.1, h.2⟩
  rw [hset]

theorem prv_insert_max_head {c : Nat} {Q : Finset Nat} {p : Nat}
    (hp : ∀ y ∈ insert c Q, y < p) : prv c (insert p Q) c = p := by
  unfold prv
  rw [ite_eq_left rfl, dite_eq_left ⟨p, mem_insert_self _ _⟩]
  apply le_antisymm
  · apply max'_le
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact Nat.le_of_lt (hp z (mem_insert_of_mem hz))
  · exact le_max' _ _ (mem_insert_self _ _)

theorem prv_insert_max_self {c : Nat} {Q : Finset Nat} {p : Nat}
    (hp : ∀ y ∈ insert c Q, y < p) : prv c (insert p Q) p = prv c Q c := by
  have hpc : p ≠ c := Nat.ne_of_gt (hp c (mem_insert_self c Q))
  unfold prv
  rw [ite_eq_right hpc, ite_eq_left rfl]
  have hset : (insert p Q).filter (· < p) = Q := by
    ext z
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | hz, hzp⟩
      · omega
      · exact hz
    · exact fun h => ⟨Or.inr h, hp z (mem_insert_of_mem h)⟩
  simp only [hset]

end Library.Combinatorics.DancingLinks
