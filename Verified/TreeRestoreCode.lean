import Verified.TreeMemory
import Verified.TreeRestore
import Verified.TreeSelect
import Verified.TreeNodeLayout

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_restoreRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} (r : Fin shape.records) {store : Store Unit} {s : Locals} {ptr : Nat}
    {p : UInt64} {slots : List Slot} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage slots.length heap store p) (hHeap : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hWidth : shape.width r = slots.length)
    (hMask : shape.mask r = maskOf slots)
    (hTag : shape.tagged = true → store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hNext : wp m rest Q (restoreRecordStore store p slots) s host) :
    wp m (restoreRecordCode shape ptr ++ rest) Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hCapacity := hRaw.capacity
  have hTop := hHeap.top
  have hPos := shape.width_pos r
  have hNat : p.toUInt32.toNat = p.toNat := by
    rw [UInt64.toNat_toUInt32]
    omega
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  have hSlotRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [hNat]
    omega
  obtain ⟨hAt1, hRaw1, -⟩ := hRaw.writeHeader hHeap (back := 40) (value := 1) (by decide)
  obtain ⟨-, hRaw2, -⟩ := hRaw1.writeHeader hAt1 (back := 24) (value := 1) (by decide)
  have hTag2 (ht : shape.tagged = true) :
      (recordHeaderWrite (recordHeaderWrite store p 40 1) p 24 1).mem.read64 p.toUInt32 =
        UInt64.ofNat (shape.ctorIndex r) := by
    rw [hRaw1.readSlot_write (back := 24) (value := 1) (by decide),
      hRaw.readSlot_write (back := 40) (value := 1) (by decide)]
    exact hTag ht
  have hTag3 (ht : shape.tagged = true) :
      (recordHeaderWrite (recordHeaderWrite (recordHeaderWrite store p 40 1) p 24 1) p 16
        (UInt64.ofNat (shape.width r))).mem.read64 p.toUInt32 =
        UInt64.ofNat (shape.ctorIndex r) := by
    rw [hRaw2.readSlot_write (back := 16) (value := UInt64.ofNat (shape.width r)) (by decide)]
    exact hTag2 ht
  simp only [restoreRecordCode, List.append_assoc]
  refine wp_headerStoreWord hPtr (hRoom 40 (by decide) (by decide)) ?_
  refine wp_headerStoreWord hPtr ?_ ?_
  · simpa only [Mem.write64_pages] using hRoom 24 (by decide) (by decide)
  refine wp_headerStorePushes hPtr ?_
    (PushesWord.selectCode r (fun r => UInt64.ofNat (shape.width r))
      (PushesWord.tag hPtr (by simpa only [Mem.write64_pages] using hSlotRoom)) hTag2) ?_
  · simpa only [Mem.write64_pages] using hRoom 16 (by decide) (by decide)
  refine wp_headerStorePushes hPtr ?_
    (PushesWord.selectCode r shape.mask
      (PushesWord.tag hPtr (by simpa only [Mem.write64_pages] using hSlotRoom)) hTag3) ?_
  · simpa only [Mem.write64_pages] using hRoom 8 (by decide) (by decide)
  simp only [restoreRecordStore, recordHeaderWrite] at hNext
  rw [← hWidth, ← hMask] at hNext
  exact hNext

theorem wp_restoreOwnedRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage slots.length heap store p) (hHeap : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hLayout : NodeLayout shape (.record slots))
    (hSlots : SlotsOwned heap store p 0 slots)
    (hApart : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint)
    (hNext : ∀ store',
      Memory.WritesRange store store' (p.toNat - 40) p.toNat → heap.At store' →
      NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) = Node.blocks store p (.record slots) →
      wp m rest Q store' s host) :
    wp m (restoreRecordCode shape ptr ++ rest) Q store s host := by
  obtain ⟨r, hLength, hMask, hPrefix, -⟩ := id hLayout
  obtain ⟨hWrites, hAt, hOwned, hBlocks, _⟩ :=
    hRaw.restore hHeap (by rw [hLength]; exact shape.width_le r) hSlots hApart
  exact wp_restoreRecord r hRaw hHeap hPtr hLength.symm hMask.symm
    (fun ht => SlotsOwned.tag hSlots hPrefix ht) (hNext _ hWrites hAt hOwned hBlocks)

#print axioms wp_restoreOwnedRecord

end Verified
