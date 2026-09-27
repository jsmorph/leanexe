import Project.ProofKit.PackedFresh
import Project.ProofKit.PackedReleaseMany

namespace Project.ProofKit.PackedReleaseMany
open Wasm Project.Runtime Project.EulerRiemann.Execution

structure Owners (before heap : Heap) (store : Store Unit) (items : List Item) : Prop where
  owned : ∀ item ∈ items, heap.OwnsPacked store item.node item.bytes
  disjoint : items.Pairwise fun a b => regionsDisjoint a.node.region b.node.region
  fresh : ∀ item ∈ items, before.FreshNode item.node

theorem Owners.nil (before heap : Heap) (store : Store Unit) : Owners before heap store [] :=
  ⟨by simp, by simp, by simp⟩

theorem Owners.frame {before heap after : Heap} {initial final : Store Unit} {items : List Item}
    (h : Owners before heap initial items) (hFrame : heap.Frame initial after final)
    (hHeap : after.At final) : Owners before after final items :=
  ⟨fun item hItem => hFrame.ownsPacked hHeap (h.owned item hItem), h.disjoint, h.fresh⟩

theorem Owners.cons {before heap after : Heap} {original initial final : Store Unit}
    {items : List Item} (h : Owners before heap initial items)
    (hBefore : before.Frame original heap initial) (hFrame : heap.Frame initial after final)
    (hHeap : after.At final) (item : Item)
    (hOwner : after.OwnsPacked final item.node item.bytes) (hFresh : heap.FreshNode item.node) :
    Owners before after final (item :: items) := by
  have hOld := h.frame hFrame hHeap
  refine ⟨?_, List.pairwise_cons.mpr ⟨?_, h.disjoint⟩, ?_⟩
  · intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact hOwner
    · exact hOld.owned other hOther
  · intro other hOther
    exact hFresh.owns_disjoint hOwner.buffer.rootBound (h.owned other hOther)
  · intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact hBefore.freshNode hFresh
    · exact h.fresh other hOther

theorem Owners.disjoint_fresh {before heap after : Heap} {initial final : Store Unit}
    {items : List Item} (h : Owners before heap initial items) {node : FreeNode} {bytes : ByteArray}
    (hOwner : after.OwnsPacked final node bytes) (hFresh : heap.FreshNode node) :
    ∀ item ∈ items, regionsDisjoint item.node.region node.region := by
  intro item hItem
  exact regionsDisjoint_symm (hFresh.owns_disjoint hOwner.buffer.rootBound (h.owned item hItem))

#print axioms Owners.cons
#print axioms Owners.disjoint_fresh

end Project.ProofKit.PackedReleaseMany
