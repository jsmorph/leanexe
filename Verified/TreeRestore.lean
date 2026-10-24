import Verified.TreeStorage

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

/-- The store after the restore of a copied record's header: count 1, kind 1, and the width
and mask of its slots. -/
def restoreRecordStore (store : Store Unit) (p : UInt64) (slots : List Slot) : Store Unit :=
  recordHeaderWrite
    (recordHeaderWrite (recordHeaderWrite (recordHeaderWrite store p 40 1) p 24 1)
      p 16 (UInt64.ofNat slots.length)) p 8 (maskOf slots)

theorem RecordStorage.restore {heap : Heap} {store : Store Unit}
    {p : UInt64} {slots : List Slot} (h : RecordStorage slots.length heap store p)
    (hHeap : heap.At store) (hShort : slots.length ≤ 64)
    (hSlots : SlotsOwned heap store p 0 slots)
    (hApart : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint) :
    let store' := restoreRecordStore store p slots
    Memory.WritesRange store store' (p.toNat - 40) p.toNat ∧ heap.At store' ∧
      NodeOwned heap store' p (.record slots) ∧
      Node.blocks store' p (.record slots) = Node.blocks store p (.record slots) ∧
      capacityAt store' p = capacityAt store p := by
  let store1 := recordHeaderWrite store p 40 1
  let store2 := recordHeaderWrite store1 p 24 1
  let store3 := recordHeaderWrite store2 p 16 (UInt64.ofNat slots.length)
  let store4 := recordHeaderWrite store3 p 8 (maskOf slots)
  obtain ⟨hAt1, hRaw1, hCap1⟩ := h.writeHeader hHeap (back := 40) (value := 1) (by decide)
  obtain ⟨hAt2, hRaw2, hCap2⟩ := hRaw1.writeHeader hAt1 (back := 24) (value := 1) (by decide)
  obtain ⟨hAt3, hRaw3, hCap3⟩ := hRaw2.writeHeader hAt2 (back := 16)
    (value := UInt64.ofNat slots.length) (by decide)
  obtain ⟨hAt4, hRaw4, hCap4⟩ := hRaw3.writeHeader hAt3 (back := 8)
    (value := maskOf slots) (by decide)
  have hBase := h.base
  have hAddress := h.address
  have hRoom := h.capacity
  have hAddr (back : UInt64) (hBack : back.toNat ≤ 40) :
      (p - back).toUInt32.toNat = p.toNat - back.toNat :=
    headerAddress_toNat (by omega) (by omega)
  have writeRange (s : Store Unit) (back value : UInt64) (hBack : back.toNat ≤ 40) :
      Memory.WritesRange s (recordHeaderWrite s p back value)
        (p.toNat - back.toNat) (p.toNat - back.toNat + 8) :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [hAddr back hBack]) (by rw [hAddr back hBack])
  have hW1 := writeRange store 40 1 (by decide)
  have hW2 := writeRange store1 24 1 (by decide)
  have hW3 := writeRange store2 16 (UInt64.ofNat slots.length) (by decide)
  have hW4 := writeRange store3 8 (maskOf slots) (by decide)
  have hTail : Memory.WritesRange store1 store4 (p.toNat - 24) p.toNat :=
    (hW2.mono (by simp) (by change p.toNat - 24 + 8 ≤ p.toNat; omega)).trans
      ((hW3.mono (by change p.toNat - 24 ≤ p.toNat - 16; omega)
        (by change p.toNat - 16 + 8 ≤ p.toNat; omega)).trans
        (hW4.mono (by change p.toNat - 24 ≤ p.toNat - 8; omega)
          (by change p.toNat - 8 + 8 ≤ p.toNat; omega)))
  have hLast : Memory.WritesRange store2 store4 (p.toNat - 16) p.toNat :=
    (hW3.mono (by simp) (by change p.toNat - 16 + 8 ≤ p.toNat; omega)).trans
      (hW4.mono (by change p.toNat - 16 ≤ p.toNat - 8; omega)
        (by change p.toNat - 8 + 8 ≤ p.toNat; omega))
  have hAll : Memory.WritesRange store store4 (p.toNat - 40) p.toNat :=
    (hW1.mono (by simp) (by change p.toNat - 40 + 8 ≤ p.toNat; omega)).trans
      (hTail.mono (by omega) (by omega))
  have hCount : store4.mem.read64 (p - 40).toUInt32 = 1 := by
    rw [hTail.read64 _ (by left; rw [hAddr 40 (by decide)]; change p.toNat - 40 + 8 ≤ p.toNat - 24; omega)]
    exact Memory.read64_write64 ..
  have hKind : store4.mem.read64 (p - 24).toUInt32 = 1 := by
    rw [hLast.read64 _ (by left; rw [hAddr 24 (by decide)]; change p.toNat - 24 + 8 ≤ p.toNat - 16; omega)]
    exact Memory.read64_write64 ..
  have hWidth : store4.mem.read64 (p - 16).toUInt32 = UInt64.ofNat slots.length := by
    rw [hW4.read64 _ (by left; rw [hAddr 16 (by decide)]; change p.toNat - 16 + 8 ≤ p.toNat - 8; omega)]
    exact Memory.read64_write64 ..
  have hMask : store4.mem.read64 (p - 8).toUInt32 = maskOf slots := Memory.read64_write64 ..
  have hSeparate := (List.pairwise_cons.mp hApart).1
  obtain ⟨hSlots4, hBlocks⟩ := SlotsOwned.frame p 0 slots hSlots (by omega)
    (fun a hLow _ => hAll.2.2 a (.inr (by omega)))
    (fun b hb => ⟨fun a hLow hHigh => hAll.2.2 a (by
      have := hSeparate b hb
      simp only [regionsDisjoint, block] at this
      omega), SlotsOwned.regions p 0 slots hSlots b hb⟩)
  have hCapacity : capacityAt store4 p = capacityAt store p := hCap4.trans (hCap3.trans (hCap2.trans hCap1))
  refine ⟨hAll, hAt4, hRaw4.record rfl hCount hKind hWidth hMask hShort hSlots4, ?_, hCapacity⟩
  change block store4 p :: slotsBlocks store4 p 0 slots = _
  rw [block_eq hCapacity, hBlocks]
  rfl

#print axioms RecordStorage.restore

end Verified
