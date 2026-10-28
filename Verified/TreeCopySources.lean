import Verified.TreeCopyFrames

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem Step.nodeBorrowedView {heap heap' : Heap} {store store' : Store Unit}
    {fresh : List (Nat × Nat)} {p : UInt64} {value : Node}
    (h : Step heap store (fun _ => True) heap' store' fresh)
    (hNode : NodeBorrowed heap store p value) (hSlotted : value.Slotted) :
    NodeBorrowed heap' store' p value ∧ value.slotRegions store' p = value.slotRegions store p ∧
      ∀ r ∈ value.slotRegions store' p, ∀ b ∈ fresh, regionsDisjoint r b := by
  have hRegions := fun r (hr : r ∈ value.slotRegions store p) =>
    h.keeps r (NodeBorrowed.regions p value hNode r hr)
      (Node.slotRegions_pos hSlotted r hr) trivial
  obtain ⟨hNode', hReads⟩ := NodeBorrowed.frame h.at_ p value hNode
    (fun r hr => ⟨(hRegions r hr).1, (hRegions r hr).2.1⟩)
  refine ⟨hNode', hReads, ?_⟩
  intro r hr
  rw [hReads] at hr
  exact (hRegions r hr).2.2

theorem Step.recordRead {heap heap' : Heap} {store store' : Store Unit}
    {fresh : List (Nat × Nat)} {p : UInt64} {slots : List LeanExe.Pipeline.Slot}
    (h : Step heap store (fun _ => True) heap' store' fresh)
    (hNode : NodeBorrowed heap store p (.record slots)) {i : Nat} (hi : i < slots.length) :
    store'.mem.read64 (slotAddress p i) = store.mem.read64 (slotAddress p i) := by
  have hAddress := hNode.1.address
  have hRegion := NodeBorrowed.regions p (.record slots) hNode (p.toNat, 8 * slots.length)
    List.mem_cons_self
  have hBytes := (h.keeps _ hRegion (by simp only; omega) trivial).1
  apply Memory.read64_congr
  intro k hk
  rw [slotAddress_toNat (by omega)]
  exact hBytes _ (by simp only; omega) (by simp only; omega)

theorem Step.childSource {heap heap' : Heap} {store store' : Store Unit}
    {fresh : List (Nat × Nat)} {p : UInt64} {slots : List LeanExe.Pipeline.Slot} {value : Node}
    (h : Step heap store (fun _ => True) heap' store' fresh)
    (hNode : NodeBorrowed heap store p (.record slots)) {i : Nat} (hi : i < slots.length)
    (hSlot : slots[i] = .child value) :
    NodeBorrowed heap store (store'.mem.read64 (slotAddress p i)) value := by
  have hValue := SlotsBorrowed.get slots 0 hNode.2 i hi
  rw [hSlot] at hValue
  rw [h.recordRead hNode hi]
  simpa only [Nat.zero_add] using hValue.1

def CopySources (shape : TreeShape) (heap : Heap) (store : Store Unit) (current : CopyRecord)
    (parents : List CopyRecord) : Prop :=
  ∀ record ∈ current :: parents, NodeLayout shape (.record record.slots) ∧
    NodeBorrowed heap store record.source (.record record.slots)

theorem CopySources.advance {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {current : CopyRecord} {parents : List CopyRecord}
    (h : CopySources shape heap store current parents) (next : Nat) :
    CopySources shape heap store { current with next } parents := by
  intro record hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h current List.mem_cons_self
  · exact h record (List.mem_cons_of_mem current hr)

theorem CopySources.apart {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {current record : CopyRecord} {parents : List CopyRecord} {fresh : List (Nat × Nat)}
    (h : CopySources shape heap0 initial current parents)
    (hStep : Step heap0 initial (fun _ => True) heap store fresh)
    (hRecord : record ∈ current :: parents) :
    ∀ r ∈ (Node.record record.slots).slotRegions store record.source,
      ∀ b ∈ fresh, regionsDisjoint r b := by
  have hSource := h record hRecord
  exact (hStep.nodeBorrowedView hSource.2 hSource.1.slotted).2.2

theorem CopySources.parentsKept {shape : TreeShape} {heap0 heap : Heap}
    {initial store : Store Unit} {current : CopyRecord} {parents : List CopyRecord}
    (h : CopySources shape heap0 initial current parents)
    (hStep : Step heap0 initial (fun _ => True) heap store (copyBlocks store current parents))
    (hApart : (copyBlocks store current parents).Pairwise regionsDisjoint) :
    ∀ record ∈ parents,
      record.Kept (fun r => regionsDisjoint r (block store current.pointer)) store := by
  have hHead : ∀ b ∈ slotsBlocks store current.pointer 0 (current.slots.take current.next) ++
      parents.flatMap (fun record => record.blocks store),
      regionsDisjoint (block store current.pointer) b := by
    simpa only [copyBlocks, CopyRecord.blocks, List.cons_append, List.append_eq] using
      (List.pairwise_cons.mp hApart).1
  intro record hr
  have hBlocks : ∀ b ∈ record.blocks store, regionsDisjoint b (block store current.pointer) := by
    intro b hb
    exact regionsDisjoint_symm (hHead b (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨record, hr, hb⟩)))
  refine ⟨hBlocks _ (by simp only [CopyRecord.blocks, List.mem_cons, true_or]), ?_, ?_⟩
  · intro r hRegion
    exact h.apart hStep (List.mem_cons_of_mem current hr) r hRegion _
      (by simp [copyBlocks, CopyRecord.blocks])
  · intro b hb
    exact hBlocks b (List.mem_cons_of_mem _ hb)

#print axioms Step.recordRead
#print axioms CopySources.parentsKept

end Verified
