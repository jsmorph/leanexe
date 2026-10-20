import Verified.TreeStorage

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def beginRecordStore (store : Store Unit) (p source parent : UInt64) : Store Unit :=
  recordHeaderWrite (recordHeaderWrite (recordHeaderWrite store p 40 parent) p 24 source) p 8 0

theorem RecordStorage.beginRecord {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {p source parent : UInt64} (h : RecordStorage shape heap store p)
    (hHeap : heap.At store) :
    let store' := beginRecordStore store p source parent
    Memory.WritesRange store store' (p.toNat - 40) p.toNat ∧ heap.At store' ∧
      RecordStorage shape heap store' p ∧ capacityAt store' p = capacityAt store p ∧
      store'.mem.read64 (p - 40).toUInt32 = parent ∧
      store'.mem.read64 (p - 24).toUInt32 = source ∧
      store'.mem.read64 (p - 8).toUInt32 = 0 := by
  obtain ⟨hAt1, hRaw1, hCap1⟩ := h.writeHeader hHeap (back := 40) (value := parent) (by decide)
  obtain ⟨hAt2, hRaw2, hCap2⟩ := hRaw1.writeHeader hAt1 (back := 24) (value := source) (by decide)
  obtain ⟨hAt3, hRaw3, hCap3⟩ := hRaw2.writeHeader hAt2 (back := 8) (value := 0) (by decide)
  refine ⟨(h.writeHeader_range (back := 40) (value := parent) (by decide)).trans
    ((hRaw1.writeHeader_range (back := 24) (value := source) (by decide)).trans
      (hRaw2.writeHeader_range (back := 8) (value := 0) (by decide))),
    hAt3, hRaw3, hCap3.trans (hCap2.trans hCap1), ?_, ?_, Memory.read64_write64 ..⟩
  · dsimp only [beginRecordStore]
    rw [hRaw2.readHeader_write (back := 8) (other := 40) (by decide) (by decide) (by decide),
      hRaw1.readHeader_write (back := 24) (other := 40) (by decide) (by decide) (by decide)]
    exact Memory.read64_write64 ..
  · dsimp only [beginRecordStore]
    rw [hRaw2.readHeader_write (back := 8) (other := 24) (by decide) (by decide) (by decide)]
    exact Memory.read64_write64 ..

#print axioms RecordStorage.beginRecord

end Verified
