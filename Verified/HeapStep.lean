import LeanExe.Pipeline.Allocation
import LeanExe.Pipeline.Records

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- A step from `heap` at `store` to `heap'` at `store'`: the allocator invariant holds after it,
the memory caps are unchanged, and every region of `heap` in `keep` keeps its bytes, is a region
of `heap'`, and lies apart from the blocks `fresh`.  The regions outside `keep` are those of the
blocks that the step consumes. -/
structure Step (heap : Heap) (store : Store Unit) (keep : Nat × Nat → Prop) (heap' : Heap)
    (store' : Store Unit) (fresh : List (Nat × Nat)) : Prop where
  at_ : heap'.At store'
  caps : store'.memoryCaps = store.memoryCaps
  keeps : ∀ r, heap.Region r → 0 < r.2 → keep r →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store'.mem.bytes a = store.mem.bytes a) ∧
      heap'.Region r ∧ ∀ b ∈ fresh, regionsDisjoint r b

namespace Step

variable {heap heap1 heap2 : Heap} {store store1 store2 : Store Unit}
  {keep keep1 keep2 : Nat × Nat → Prop} {fresh fresh1 fresh2 : List (Nat × Nat)}

theorem refl (h : heap.At store) (keep : Nat × Nat → Prop) : Step heap store keep heap store [] :=
  ⟨h, rfl, fun _ hr _ _ => ⟨fun _ _ _ => rfl, hr, nofun⟩⟩

/-- Two steps in a row, the second keeping what the first keeps and leaves apart from its
blocks. -/
theorem transBoth (h1 : Step heap store keep1 heap1 store1 fresh1)
    (h2 : Step heap1 store1 keep2 heap2 store2 fresh2)
    (hKeep : ∀ r, keep r → keep1 r ∧ ((∀ b ∈ fresh1, regionsDisjoint r b) → keep2 r)) :
    Step heap store keep heap2 store2 (fresh1 ++ fresh2) := by
  refine ⟨h2.at_, h2.caps.trans h1.caps, fun r hr hpos hk => ?_⟩
  obtain ⟨hk1, hk2⟩ := hKeep r hk
  obtain ⟨hBytes1, hRegion1, hFresh1⟩ := h1.keeps r hr hpos hk1
  obtain ⟨hBytes2, hRegion2, hFresh2⟩ := h2.keeps r hRegion1 hpos (hk2 hFresh1)
  refine ⟨fun a hl hh => (hBytes2 a hl hh).trans (hBytes1 a hl hh), hRegion2, fun b hb => ?_⟩
  rcases List.mem_append.mp hb with hb | hb
  · exact hFresh1 b hb
  · exact hFresh2 b hb

theorem trans (h1 : Step heap store keep1 heap1 store1 fresh1)
    (h2 : Step heap1 store1 keep2 heap2 store2 fresh2)
    (hKeep : ∀ r, keep r → keep1 r ∧ ((∀ b ∈ fresh1, regionsDisjoint r b) → keep2 r)) :
    Step heap store keep heap2 store2 fresh2 :=
  let h := h1.transBoth h2 hKeep
  ⟨h.at_, h.caps, fun r hr hpos hk => by
    obtain ⟨hb, hreg, hf⟩ := h.keeps r hr hpos hk
    exact ⟨hb, hreg, fun b hb' => hf b (List.mem_append_right _ hb')⟩⟩

/-- A step for fewer kept regions and fewer fresh blocks. -/
theorem mono (h : Step heap store keep1 heap1 store1 fresh1) {keep' : Nat × Nat → Prop}
    {fresh' : List (Nat × Nat)} (hKeep : ∀ r, keep' r → keep1 r)
    (hFresh : ∀ b ∈ fresh', b ∈ fresh1) : Step heap store keep' heap1 store1 fresh' :=
  ⟨h.at_, h.caps, fun r hr hpos hk => by
    obtain ⟨hb, hreg, hf⟩ := h.keeps r hr hpos (hKeep r hk)
    exact ⟨hb, hreg, fun b hb' => hf b (hFresh b hb')⟩⟩

theorem cap (h : Step heap store keep heap1 store1 fresh) (m : Module) :
    store1.memoryCap m 0 = store.memoryCap m 0 := by
  simp [Store.memoryCap, h.caps]

theorem borrowed (h : Step heap store keep heap1 store1 fresh) {p : UInt64} {xs : Array UInt64}
    (hp : heap.Borrowed store p xs) (hk : keep (p.toNat, 8 * (xs.size + 1))) :
    heap1.Borrowed store1 p xs ∧ ∀ b ∈ fresh, regionsDisjoint (p.toNat, 8 * (xs.size + 1)) b := by
  obtain ⟨hBytes, hRegion, hFresh⟩ := h.keeps _ hp.region (by show 0 < 8 * (xs.size + 1); omega) hk
  exact ⟨hp.keepIn h.at_ hBytes hRegion, hFresh⟩

theorem owned (h : Step heap store keep heap1 store1 fresh) {p : UInt64} {xs : Array UInt64}
    (hp : heap.Owned store p xs) (hk : keep (block store p)) :
    (heap1.Owned store1 p xs ∧ capacityAt store1 p = capacityAt store p) ∧
      ∀ b ∈ fresh, regionsDisjoint (block store p) b := by
  obtain ⟨hBytes, hRegion, hFresh⟩ := h.keeps _ hp.region (by simp [block]) hk
  exact ⟨hp.keepIn h.at_ hBytes hRegion, hFresh⟩

end Step


end Verified
