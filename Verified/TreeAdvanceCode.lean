import Verified.TreeSlotCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_copyRecordAdvance {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr index value : Nat}
    {parent word : UInt64} {record : CopyRecord} {rest : Program} {Q : Assertion Unit}
    (h : record.Holds shape heap store parent) (hAt : heap.At store)
    (hBound : record.next < record.slots.length)
    (hValue : (record.slots[record.next]).ValueOwned heap store word)
    (hSourceApart : ∀ r ∈ (Node.record record.slots).slotRegions store record.source,
      regionsDisjoint r (block store record.pointer))
    (hPrefixApart : ∀ b ∈ slotsBlocks store record.pointer 0 (record.slots.take record.next),
      regionsDisjoint b (block store record.pointer))
    (hValueApart : ∀ b ∈ (record.slots[record.next]).valueBlocks store word,
      regionsDisjoint b (block store record.pointer))
    (hPtr : s.get ptr = some (.i64 record.pointer))
    (hIndex : s.get index = some (.i64 (UInt64.ofNat record.next)))
    (hWord : s.get value = some (.i64 word))
    (hNext : ∀ store',
      CopyRecord.Holds shape heap store' parent { record with next := record.next + 1 } →
      Step heap store (fun r => regionsDisjoint r (block store record.pointer)) heap store' [] →
      ({ record with next := record.next + 1 } : CopyRecord).blocks store' =
        record.blocks store ++ (record.slots[record.next]).valueBlocks store word →
      wp m rest Q store' s host) :
    wp m (treeSlotAddress ptr index ++ [.localGet value, .store64 0] ++
      treeCopyAdvance ptr index ++ rest) Q store s host := by
  obtain ⟨hRecord, hStep, hBlocks⟩ := h.advance hAt hBound hValue
    hSourceApart hPrefixApart hValueApart
  have hBase := h.storage.base
  have hAddress := h.storage.address
  have hCapacity := h.storage.capacity
  have hBelow := h.storage.below
  have hTop := hAt.top
  rw [List.append_assoc, List.append_assoc]
  refine wp_treeSlotStore hPtr hIndex hWord ?_ ?_
  · rw [slotAddress_toNat (by omega)]
    omega
  refine wp_treeCopyAdvance hPtr hIndex ?_ (hNext _ hRecord hStep hBlocks)
  simp only [Mem.write64_pages]
  rw [headerAddress_toNat (by change 8 ≤ record.pointer.toNat; omega) (by omega)]
  change record.pointer.toNat - 8 + 8 ≤ store.mem.pages * 65536
  omega

#print axioms wp_copyRecordAdvance

end Verified
