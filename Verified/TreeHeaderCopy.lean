import Verified.TreeAllocate
import Verified.TreeDetach

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def copyHeaderStore (shape : TreeShape) (r : Fin shape.records) (store : Store Unit) (p : UInt64) :
    Store Unit :=
  recordHeaderWrite (recordHeaderWrite store p 24 1) p 16 (UInt64.ofNat (shape.width r))

theorem RecordStorage.copyHeader {shape : TreeShape} {r : Fin shape.records} {heap : Heap}
    {store : Store Unit} {p : UInt64} (h : RecordStorage (shape.width r) heap store p)
    (hAt : heap.At store)
    (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hMask : store.mem.read64 (p - 8).toUInt32 = 0) :
    let store' := copyHeaderStore shape r store p
    Memory.WritesRange store store' (p.toNat - 40) p.toNat ∧ heap.At store' ∧
      TreeHeader.Owned shape r heap store' p ∧ capacityAt store' p = capacityAt store p := by
  obtain ⟨hAt1, hRaw1, hCap1⟩ := h.writeHeader hAt (back := 24) (value := 1) (by decide)
  obtain ⟨hAt2, hRaw2, hCap2⟩ := hRaw1.writeHeader hAt1 (back := 16)
    (value := UInt64.ofNat (shape.width r)) (by decide)
  have hReadCount : (copyHeaderStore shape r store p).mem.read64 (p - 40).toUInt32 = 1 := by
    dsimp only [copyHeaderStore]
    rw [hRaw1.readHeader_write (back := 16) (other := 40) (by decide) (by decide) (by decide),
      h.readHeader_write (back := 24) (other := 40) (by decide) (by decide) (by decide)]
    exact hCount
  have hReadMask : (copyHeaderStore shape r store p).mem.read64 (p - 8).toUInt32 = 0 := by
    dsimp only [copyHeaderStore]
    rw [hRaw1.readHeader_write (back := 16) (other := 8) (by decide) (by decide) (by decide),
      h.readHeader_write (back := 24) (other := 8) (by decide) (by decide) (by decide)]
    exact hMask
  have hReadKind : (copyHeaderStore shape r store p).mem.read64 (p - 24).toUInt32 = 1 := by
    dsimp only [copyHeaderStore]
    rw [hRaw1.readHeader_write (back := 16) (other := 24) (by decide) (by decide) (by decide)]
    exact Memory.read64_write64 ..
  let words := recordWords (copyHeaderStore shape r store p) p 0 (shape.width r)
  have hLength : (words.map Slot.word).length = shape.width r := by
    simp only [List.length_map, words, recordWords_length]
  refine ⟨(h.writeHeader_range (back := 24) (value := 1) (by decide)).trans
    (hRaw1.writeHeader_range (back := 16) (value := UInt64.ofNat (shape.width r)) (by decide)),
    hAt2, ⟨words, recordWords_length .., ?_⟩, hCap2.trans hCap1⟩
  exact hRaw2.record hLength hReadCount hReadKind (Memory.read64_write64 ..)
    (by rw [wordSlots_mask]; exact hReadMask) (shape.width_le r) (recordWords_owned ..)
    (wordSlots_lengths _)

#print axioms Step.allocate
#print axioms RecordStorage.copyHeader

end Verified
