import Verified.TreeDetach

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def TreeHeader.setMask (store : Store Unit) (p mask : UInt64) : Store Unit :=
  { store with mem := store.mem.write64 (p - 8).toUInt32 mask }

theorem TreeHeader.attach_spec {shape : TreeShape} {r : Fin shape.records} {heap : Heap}
    {store : Store Unit} {p : UInt64} {slots : List Slot}
    (hHeap : heap.At store) (hHeader : Owned shape r heap store p)
    (hLength : slots.length = shape.width r) (hSlots : SlotsOwned heap store p 0 slots)
    (hApart : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint) :
    let store' := setMask store p (maskOf slots)
    Memory.WritesRange store store' (p.toNat - 8) p.toNat ∧ heap.At store' ∧
      NodeOwned heap store' p (.record slots) ∧
      Node.blocks store' p (.record slots) = Node.blocks store p (.record slots) := by
  obtain ⟨words, hWords, hHead, _⟩ := hHeader
  have hBase := hHead.base
  have hAddress := hHead.address
  have hRoom := hHead.capacity
  have hLength' : slots.length = (words.map Slot.word).length := by
    simp only [List.length_map, hWords, hLength]
  let store' := setMask store p (maskOf slots)
  have hAddr : (p - 8).toUInt32.toNat = p.toNat - 8 :=
    headerAddress_toNat (by change 8 ≤ p.toNat; omega) (by omega)
  have hWrites : Memory.WritesRange store store' (p.toNat - 8) p.toNat :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [hAddr]) (by rw [hAddr]; omega)
  have hRead (back : UInt64) (h16 : 16 ≤ back.toNat) (h48 : back.toNat ≤ 48) :
      store'.mem.read64 (p - back).toUInt32 = store.mem.read64 (p - back).toUInt32 := by
    apply hWrites.read64
    left
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  have hCapacity : capacityAt store' p = capacityAt store p := by
    unfold capacityAt
    rw [hRead 32 (by decide) (by decide)]
  have hHead' : RecordHeader heap store' p slots := by
    refine ⟨hBase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hRead 48 (by decide) (by decide)]; exact hHead.magic
    · rw [hRead 40 (by decide) (by decide)]; exact hHead.count
    · rw [hRead 24 (by decide) (by decide)]; exact hHead.kind
    · rw [hRead 16 (by decide) (by decide), hLength']; exact hHead.width
    · exact Memory.read64_write64 ..
    · rw [hLength']; exact hHead.short
    · rw [hLength', hCapacity]; exact hHead.capacity
    · rw [hCapacity]; exact hHead.address
    · rw [hCapacity]; exact hHead.below
    · rw [hCapacity]; exact hHead.separate
  have hSeparate := (List.pairwise_cons.mp hApart).1
  obtain ⟨hSlots', hBlocks⟩ := SlotsOwned.frame p 0 slots hSlots (by omega)
    (fun a hLow _ => hWrites.2.2 a (.inr (by omega)))
    (fun b hb => ⟨fun a hLow hHigh => hWrites.2.2 a (by
      have := hSeparate b hb
      simp only [regionsDisjoint, block] at this
      omega), SlotsOwned.regions p 0 slots hSlots b hb⟩)
  refine ⟨hWrites, hHeap.writesApart hWrites ?_, ⟨hHead', hSlots'⟩, ?_⟩
  · intro node hNode
    have := hHead.separate node hNode
    simp only [regionsDisjoint] at this ⊢
    omega
  · change block store' p :: slotsBlocks store' p 0 slots = _
    rw [block_eq hCapacity, hBlocks]
    rfl

#print axioms TreeHeader.attach_spec

end Verified
