import Verified.TreeCopyState
import Verified.HeapStep
import LeanExe.Pipeline.Rebuilt

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem Step.nodeBorrowed {heap heap' : Heap} {store store' : Store Unit}
    {fresh : List (Nat × Nat)} {p : UInt64} {value : Node}
    (h : Step heap store (fun _ => True) heap' store' fresh)
    (hNode : NodeBorrowed heap store p value) (hSlotted : value.Slotted) :
    NodeBorrowed heap' store' p value ∧
      ∀ r ∈ value.slotRegions store p, ∀ b ∈ fresh, regionsDisjoint r b := by
  have hRegions := fun r (hr : r ∈ value.slotRegions store p) =>
    h.keeps r (NodeBorrowed.regions p value hNode r hr)
      (Node.slotRegions_pos hSlotted r hr) trivial
  obtain ⟨hNode', _⟩ := NodeBorrowed.frame h.at_ p value hNode
    (fun r hr => ⟨(hRegions r hr).1, (hRegions r hr).2.1⟩)
  exact ⟨hNode', fun r hr => (hRegions r hr).2.2⟩

theorem CopyRecord.Holds.stepKeeping {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {parent : UInt64} {record : CopyRecord}
    {fresh : List (Nat × Nat)} {keep : Nat × Nat → Prop}
    (h : record.Holds shape heap store parent) (hStep : Step heap store keep heap' store' fresh)
    (hRawKeep : keep (block store record.pointer))
    (hSourceKeep : ∀ r ∈ (Node.record record.slots).slotRegions store record.source, keep r)
    (hChildKeep : ∀ b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next), keep b) :
    record.Holds shape heap' store' parent ∧ record.blocks store' = record.blocks store ∧
      ∀ b ∈ record.blocks store, ∀ f ∈ fresh, regionsDisjoint b f := by
  have hRaw := hStep.keeps (block store record.pointer) h.storage.region
    (by simp [block]) hRawKeep
  have hSource := fun r (hr : r ∈ (Node.record record.slots).slotRegions store record.source) =>
    hStep.keeps r (NodeBorrowed.regions record.source (.record record.slots) h.borrowed r hr)
      (Node.slotRegions_pos h.layout.slotted r hr) (hSourceKeep r hr)
  have hChildren := fun b (hb : b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next)) =>
    hStep.keeps b (SlotsOwned.regions record.pointer 0 _ h.filled b hb)
      (slotsBlocks_pos store record.pointer 0 _ b hb) (hChildKeep b hb)
  have hBase := h.storage.base
  obtain ⟨hRecord, hBlocks⟩ := h.frame
    (fun a hLow hHigh => hRaw.1 a (by simp only [block]; omega)
      (by simp only [block]; omega)) hRaw.2.1
    (fun r hr => ⟨(hSource r hr).1, (hSource r hr).2.1⟩)
    (fun b hb => ⟨(hChildren b hb).1, (hChildren b hb).2.1⟩) hStep.at_
  refine ⟨hRecord, hBlocks, fun b hb => ?_⟩
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hRaw.2.2
  · exact (hChildren b hb).2.2

theorem CopyRecord.Holds.step {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {parent : UInt64} {record : CopyRecord}
    {fresh : List (Nat × Nat)} (h : record.Holds shape heap store parent)
    (hStep : Step heap store (fun _ => True) heap' store' fresh) :
    record.Holds shape heap' store' parent ∧ record.blocks store' = record.blocks store ∧
      ∀ b ∈ record.blocks store, ∀ f ∈ fresh, regionsDisjoint b f :=
  h.stepKeeping hStep trivial (fun _ _ => trivial) (fun _ _ => trivial)

#print axioms CopyRecord.Holds.step
#print axioms Step.writeFresh

end Verified
