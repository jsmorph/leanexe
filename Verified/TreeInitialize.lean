import Verified.TreeStorage

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def linkRecordStore (store : Store Unit) (p source parent : UInt64) : Store Unit :=
  recordHeaderWrite (recordHeaderWrite (recordHeaderWrite store p 40 parent) p 24 source) p 8 0

/-- The store after the start of a record's copy: the width word, when the shape is tagged, then
the parent link, the source pointer, and the next slot index. -/
def beginRecordStore (tagged : Bool) (store : Store Unit) (p source parent : UInt64)
    (size : Nat) : Store Unit :=
  linkRecordStore (if tagged then recordHeaderWrite store p 16 (UInt64.ofNat size) else store)
    p source parent

theorem RecordStorage.linkRecord {width : Nat} {heap : Heap} {store : Store Unit}
    {p source parent : UInt64} (h : RecordStorage width heap store p)
    (hHeap : heap.At store) :
    let store' := linkRecordStore store p source parent
    Memory.WritesRange store store' (p.toNat - 40) p.toNat ∧ heap.At store' ∧
      RecordStorage width heap store' p ∧ capacityAt store' p = capacityAt store p ∧
      store'.mem.read64 (p - 40).toUInt32 = parent ∧
      store'.mem.read64 (p - 24).toUInt32 = source ∧
      store'.mem.read64 (p - 16).toUInt32 = store.mem.read64 (p - 16).toUInt32 ∧
      store'.mem.read64 (p - 8).toUInt32 = 0 := by
  obtain ⟨hAt1, hRaw1, hCap1⟩ := h.writeHeader hHeap (back := 40) (value := parent) (by decide)
  obtain ⟨hAt2, hRaw2, hCap2⟩ := hRaw1.writeHeader hAt1 (back := 24) (value := source) (by decide)
  obtain ⟨hAt3, hRaw3, hCap3⟩ := hRaw2.writeHeader hAt2 (back := 8) (value := 0) (by decide)
  refine ⟨(h.writeHeader_range (back := 40) (value := parent) (by decide)).trans
    ((hRaw1.writeHeader_range (back := 24) (value := source) (by decide)).trans
      (hRaw2.writeHeader_range (back := 8) (value := 0) (by decide))),
    hAt3, hRaw3, hCap3.trans (hCap2.trans hCap1), ?_, ?_, ?_, Memory.read64_write64 ..⟩
  · dsimp only [linkRecordStore]
    rw [hRaw2.readHeader_write (back := 8) (other := 40) (by decide) (by decide) (by decide),
      hRaw1.readHeader_write (back := 24) (other := 40) (by decide) (by decide) (by decide)]
    exact Memory.read64_write64 ..
  · dsimp only [linkRecordStore]
    rw [hRaw2.readHeader_write (back := 8) (other := 24) (by decide) (by decide) (by decide)]
    exact Memory.read64_write64 ..
  · dsimp only [linkRecordStore]
    rw [hRaw2.readHeader_write (back := 8) (other := 16) (by decide) (by decide) (by decide),
      hRaw1.readHeader_write (back := 24) (other := 16) (by decide) (by decide) (by decide),
      h.readHeader_write (back := 40) (other := 16) (by decide) (by decide) (by decide)]

theorem RecordStorage.beginRecord {width : Nat} {heap : Heap} {store : Store Unit}
    {p source parent : UInt64} (tagged : Bool) (size : Nat) (h : RecordStorage width heap store p)
    (hHeap : heap.At store) :
    let store' := beginRecordStore tagged store p source parent size
    Memory.WritesRange store store' (p.toNat - 40) p.toNat ∧ heap.At store' ∧
      RecordStorage width heap store' p ∧ capacityAt store' p = capacityAt store p ∧
      store'.mem.read64 (p - 40).toUInt32 = parent ∧
      store'.mem.read64 (p - 24).toUInt32 = source ∧
      store'.mem.read64 (p - 8).toUInt32 = 0 ∧
      (tagged = true → store'.mem.read64 (p - 16).toUInt32 = UInt64.ofNat size) := by
  cases tagged with
  | false =>
    obtain ⟨hWrites, hAt, hRaw, hCap, hParent, hSource, -, hIndex⟩ :=
      h.linkRecord hHeap (source := source) (parent := parent)
    exact ⟨hWrites, hAt, hRaw, hCap, hParent, hSource, hIndex, fun h => absurd h (by decide)⟩
  | true =>
    obtain ⟨hAt0, hRaw0, hCap0⟩ := h.writeHeader hHeap (back := 16)
      (value := UInt64.ofNat size) (by decide)
    obtain ⟨hWrites, hAt, hRaw, hCap, hParent, hSource, hWidth, hIndex⟩ :=
      hRaw0.linkRecord hAt0 (source := source) (parent := parent)
    refine ⟨(h.writeHeader_range (back := 16) (value := UInt64.ofNat size) (by decide)).trans
      hWrites, hAt, hRaw, hCap.trans hCap0, hParent, hSource, hIndex, fun _ => ?_⟩
    rw [beginRecordStore, ite_eq_left (rfl : true = true), hWidth]
    exact Memory.read64_write64 ..

#print axioms RecordStorage.beginRecord

end Verified
