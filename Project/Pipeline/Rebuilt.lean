import Project.Pipeline.Records

/-!
Values rebuilt from consumed records.  A function that consumes a value may rewrite its records
in place and allocate new ones; `Heap.Rebuilt` states what such a function leaves: the result
owned with disjoint blocks, and every region apart from the consumed blocks with its bytes,
still a region, and apart from the result.
-/

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/-- The value `n`, owned at `p` in `heap'` and `store`, made from `heap` and `initial` by code
that consumed the blocks `gone`. -/
structure Heap.Rebuilt (heap : Heap) (initial : Store Unit) (gone : List (Nat × Nat))
    (heap' : Heap) (store : Store Unit) (p : UInt64) (n : Node) : Prop where
  at_ : heap'.At store
  owned : NodeOwned heap' store p n
  disjoint : (n.blocks store p).Pairwise regionsDisjoint
  region : ∀ r, heap.Region r → 0 < r.2 → (∀ b ∈ gone, regionsDisjoint r b) →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧
      heap'.Region r ∧ ∀ b ∈ n.blocks store p, regionsDisjoint r b
  pages : initial.mem.pages ≤ store.mem.pages
  caps : store.memoryCaps = initial.memoryCaps

/-- The null pointer is the empty value, rebuilt from any heap. -/
theorem Heap.Rebuilt.null {heap : Heap} {initial : Store Unit} {gone : List (Nat × Nat)}
    (h : heap.At initial) : heap.Rebuilt initial gone heap initial 0 .null :=
  ⟨h, rfl, .nil, fun _ hr _ _ => ⟨fun _ _ _ => rfl, hr, fun _ hb => nomatch hb⟩, le_refl _, rfl⟩

/-- An owned value with disjoint blocks is rebuilt from its own blocks by code that leaves it
as it is. -/
theorem Heap.Rebuilt.refl {heap : Heap} {store : Store Unit} {p : UInt64} {n : Node}
    (hHeap : heap.At store) (h : NodeOwned heap store p n)
    (hd : (n.blocks store p).Pairwise regionsDisjoint) :
    heap.Rebuilt store (n.blocks store p) heap store p n :=
  ⟨hHeap, h, hd, fun _ hr _ hGone => ⟨fun _ _ _ => rfl, hr, fun b hb => hGone b hb⟩, le_refl _,
    rfl⟩

/-- A value built without consuming anything is rebuilt from any blocks. -/
theorem Heap.Built.rebuilt {heap heap' : Heap} {initial store : Store Unit} {p : UInt64}
    {n : Node} (h : heap.Built initial heap' store p n) (gone : List (Nat × Nat)) :
    heap.Rebuilt initial gone heap' store p n :=
  ⟨h.at_, h.owned, h.disjoint, fun r hr _ _ => h.region r hr, h.pages, h.caps⟩

/-- Every block has positive length. -/
theorem block_pos (store : Store Unit) (q : UInt64) : 0 < (block store q).2 := by
  simp [block]

mutual
/-- Every block of a value has positive length. -/
theorem Node.blocks_pos (store : Store Unit) : ∀ (p : UInt64) (n : Node),
    ∀ b ∈ Node.blocks store p n, 0 < b.2
  | _, .null, _, hb => nomatch hb
  | p, .record slots, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact block_pos store p
      · exact slotsBlocks_pos store p 0 slots b hb

theorem slotsBlocks_pos (store : Store Unit) : ∀ (p : UInt64) (i : Nat) (slots : List Slot),
    ∀ b ∈ slotsBlocks store p i slots, 0 < b.2
  | _, _, [], _, hb => nomatch hb
  | p, i, .word _ :: rest, b, hb => slotsBlocks_pos store p (i + 1) rest b hb
  | p, i, .child n :: rest, b, hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact Node.blocks_pos store _ n b hb
      · exact slotsBlocks_pos store p (i + 1) rest b hb
end

/-- A value owned before a call that consumed `gone`, apart from `gone`, stays owned with the
same blocks and lies apart from the call's result. -/
theorem Heap.Rebuilt.keepNode {heap heap' : Heap} {initial store : Store Unit}
    {gone : List (Nat × Nat)} {p q : UInt64} {n m : Node}
    (h : heap.Rebuilt initial gone heap' store p n) (hm : NodeOwned heap initial q m)
    (hApart : ∀ b ∈ m.blocks initial q, ∀ g ∈ gone, regionsDisjoint b g) :
    NodeOwned heap' store q m ∧ m.blocks store q = m.blocks initial q ∧
      ∀ b ∈ m.blocks initial q, ∀ c ∈ n.blocks store p, regionsDisjoint b c := by
  have hRegions := NodeOwned.regions q m hm
  have hKeep := fun b (hb : b ∈ m.blocks initial q) =>
    h.region b (hRegions b hb) (Node.blocks_pos initial q m b hb) (hApart b hb)
  obtain ⟨hOwned, hBlocks⟩ := NodeOwned.frame q m hm fun b hb => ⟨(hKeep b hb).1, (hKeep b hb).2.1⟩
  exact ⟨hOwned, hBlocks, fun b hb => (hKeep b hb).2.2⟩

/-- A borrowed array apart from the consumed blocks stays borrowed and lies apart from the
result. -/
theorem Heap.Rebuilt.keepBorrowed {heap heap' : Heap} {initial store : Store Unit}
    {gone : List (Nat × Nat)} {p q : UInt64} {n : Node} {ws : Array UInt64}
    (h : heap.Rebuilt initial gone heap' store p n) (hq : heap.Borrowed initial q ws)
    (hApart : ∀ b ∈ gone, regionsDisjoint (q.toNat, 8 * (ws.size + 1)) b) :
    heap'.Borrowed store q ws ∧
      ∀ b ∈ n.blocks store p, regionsDisjoint (q.toNat, 8 * (ws.size + 1)) b := by
  obtain ⟨hBytes, hRegion, hOut⟩ := h.region _ hq.region (by show 0 < 8 * (ws.size + 1); omega)
    hApart
  exact ⟨hq.keep h.pages hBytes hRegion, hOut⟩

/-- An owned array apart from the consumed blocks stays owned, with the same capacity, and lies
apart from the result. -/
theorem Heap.Rebuilt.keepOwned {heap heap' : Heap} {initial store : Store Unit}
    {gone : List (Nat × Nat)} {p q : UInt64} {n : Node} {ws : Array UInt64}
    (h : heap.Rebuilt initial gone heap' store p n) (hq : heap.Owned initial q ws)
    (hApart : ∀ b ∈ gone, regionsDisjoint (block initial q) b) :
    (heap'.Owned store q ws ∧ capacityAt store q = capacityAt initial q) ∧
      ∀ b ∈ n.blocks store p, regionsDisjoint (block initial q) b := by
  obtain ⟨hBytes, hRegion, hOut⟩ := h.region _ hq.region (block_pos initial q) hApart
  exact ⟨hq.keep h.pages hBytes hRegion, hOut⟩

/-- The node case of a consumed recursion over a record `[child, word, child]`: the two
children rebuilt by consecutive calls, then the record's three slots written. -/
theorem Heap.Rebuilt.node {heap heap1 heap2 : Heap} {initial store1 store2 final : Store Unit}
    {p q1 q2 k k' : UInt64} {nl nr ml mr : Node}
    (hOwned : NodeOwned heap initial p (.record [.child nl, .word k, .child nr]))
    (hDisjoint : (Node.blocks initial p (.record [.child nl, .word k, .child nr])).Pairwise
      regionsDisjoint)
    (h1 : heap.Rebuilt initial (nl.blocks initial (initial.mem.read64 (slotAddress p 0)))
      heap1 store1 q1 ml)
    (h2 : heap1.Rebuilt store1 (nr.blocks store1 (initial.mem.read64 (slotAddress p 2)))
      heap2 store2 q2 mr)
    (hWrites : Memory.WritesRange store2 final p.toNat (p.toNat + 24))
    (hq1 : final.mem.read64 (slotAddress p 0) = q1)
    (hk' : final.mem.read64 (slotAddress p 1) = k')
    (hq2 : final.mem.read64 (slotAddress p 2) = q2) :
    heap.Rebuilt initial (Node.blocks initial p (.record [.child nl, .word k, .child nr])) heap2
      final p (.record [.child ml, .word k', .child mr]) := by
  obtain ⟨hHead, hl, -, hr, -⟩ := hOwned
  simp only [Nat.zero_add, Nat.reduceAdd] at hr
  have hBlocks : Node.blocks initial p (.record [.child nl, .word k, .child nr]) =
      block initial p :: (nl.blocks initial (initial.mem.read64 (slotAddress p 0)) ++
        nr.blocks initial (initial.mem.read64 (slotAddress p 2))) := by
    simp [Node.blocks, slotsBlocks]
  rw [hBlocks] at hDisjoint ⊢
  obtain ⟨hP0, hPlr⟩ := List.pairwise_cons.mp hDisjoint
  obtain ⟨-, -, hlr⟩ := List.pairwise_append.mp hPlr
  have hRoom := hHead.capacity
  have hBase := hHead.base
  simp only [List.length_cons, List.length_nil] at hRoom
  have hPosP := block_pos initial p
  -- The first call keeps the record's block, and the right child.
  obtain ⟨hBytesP1, hRegP1, hApartP1⟩ := h1.region _ hHead.region hPosP
    fun b hb => hP0 b (List.mem_append_left _ hb)
  obtain ⟨-, hrBlocks1, hrApart1⟩ := h1.keepNode hr
    fun b hb g hg => regionsDisjoint_symm (hlr g hg b hb)
  -- The second call keeps the record's block and the first call's result.
  obtain ⟨hBytesP2, hRegP2, hApartP2⟩ := h2.region _ hRegP1 hPosP fun b hb => by
    rw [hrBlocks1] at hb
    exact hP0 b (List.mem_append_right _ hb)
  obtain ⟨hl2, hlBlocks2, hlApart2⟩ := h2.keepNode h1.owned fun b hb g hg => by
    rw [hrBlocks1] at hg
    exact regionsDisjoint_symm (hrApart1 g hg b hb)
  -- The writes change only the record's slots.
  have hOutside : ∀ b, regionsDisjoint (block initial p) b → ∀ a, b.1 ≤ a → a < b.1 + b.2 →
      final.mem.bytes a = store2.mem.bytes a := fun b hb a hLow hHigh =>
    hWrites.2.2 a (by simp only [regionsDisjoint, block] at hb; omega)
  obtain ⟨hHead', hCapacity⟩ := hHead.rewrite (heap' := heap2) (store' := final)
    (slots' := [.child ml, .word k', .child mr])
    (fun a hLow hHigh => (hWrites.2.2 a (.inl hHigh)).trans ((hBytesP2 a
      (by simp only [block]; omega) (by simp only [block]; omega)).trans
      (hBytesP1 a (by simp only [block]; omega) (by simp only [block]; omega))))
    rfl rfl hRegP2
  obtain ⟨hlF, hlBlocksF⟩ := NodeOwned.frame q1 ml hl2 fun b hb =>
    ⟨hOutside b (hApartP1 b (hlBlocks2 ▸ hb)), NodeOwned.regions q1 ml hl2 b hb⟩
  obtain ⟨hrF, hrBlocksF⟩ := NodeOwned.frame q2 mr h2.owned fun b hb =>
    ⟨hOutside b (hApartP2 b hb), NodeOwned.regions q2 mr h2.owned b hb⟩
  have hNewBlocks : Node.blocks final p (.record [.child ml, .word k', .child mr]) =
      block initial p :: (ml.blocks store1 q1 ++ mr.blocks store2 q2) := by
    simp only [Node.blocks, slotsBlocks, Nat.zero_add, Nat.reduceAdd, List.append_nil, hq1, hq2,
      hlBlocksF, hlBlocks2, hrBlocksF, block_eq hCapacity]
  refine ⟨h2.at_.writesApart hWrites fun node hNode => ?_, ⟨hHead', ?_, hk', ?_, trivial⟩, ?_,
    fun r hr hpos hGone => ?_, h1.pages.trans (h2.pages.trans (le_of_eq hWrites.2.1.symm)), ?_⟩
  · have := hRegP2.separate node hNode
    simp only [regionsDisjoint, block] at this ⊢
    omega
  · rw [hq1]; exact hlF
  · show NodeOwned heap2 final (final.mem.read64 (slotAddress p 2)) mr
    rw [hq2]; exact hrF
  · rw [hNewBlocks]
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, List.pairwise_append.mpr
      ⟨h1.disjoint, h2.disjoint, hlApart2⟩⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hApartP1 b hb
    · exact hApartP2 b hb
  · obtain ⟨hB1, hR1, hA1⟩ := h1.region r hr hpos
      fun b hb => hGone b (List.mem_cons_of_mem _ (List.mem_append_left _ hb))
    obtain ⟨hB2, hR2, hA2⟩ := h2.region r hR1 hpos fun b hb => by
      rw [hrBlocks1] at hb
      exact hGone b (List.mem_cons_of_mem _ (List.mem_append_right _ hb))
    have hRP := hGone (block initial p) List.mem_cons_self
    refine ⟨fun a hLow hHigh => (hWrites.2.2 a ?_).trans ((hB2 a hLow hHigh).trans
      (hB1 a hLow hHigh)), hR2, ?_⟩
    · simp only [regionsDisjoint, block] at hRP
      omega
    · rw [hNewBlocks]
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hRP
      rcases List.mem_append.mp hb with hb | hb
      · exact hA1 b hb
      · exact hA2 b hb
  · rw [hWrites.1]
    exact h2.caps.trans h1.caps

end Project.Pipeline
