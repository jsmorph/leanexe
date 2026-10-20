import Verified.TreeMemory
import Verified.TreeRestore

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_restoreRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {rest : Program} {Q : Assertion Unit} (hRaw : RecordStorage shape heap store p)
    (hHeap : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (restoreRecordStore shape store p) s host) :
    wp m (restoreRecordCode shape ptr ++ rest) Q store s host := by
  have hBase := hRaw.base
  have hAddress := hRaw.address
  have hBelow := hRaw.below
  have hTop := hHeap.top
  have hRoom (back : UInt64) (h8 : 8 ≤ back.toNat) (h40 : back.toNat ≤ 40) :
      (p - back).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  simp only [restoreRecordCode, List.append_assoc]
  refine wp_headerStoreWord hPtr (hRoom 40 (by decide) (by decide)) ?_
  refine wp_headerStoreWord hPtr ?_ ?_
  · simpa only [Mem.write64_pages] using hRoom 24 (by decide) (by decide)
  refine wp_headerStoreWord hPtr ?_ ?_
  · simpa only [Mem.write64_pages] using hRoom 16 (by decide) (by decide)
  refine wp_headerStoreWord hPtr ?_ ?_
  · simpa only [Mem.write64_pages] using hRoom 8 (by decide) (by decide)
  exact hNext

theorem wp_restoreOwnedRecord {m : Module} {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {store : Store Unit} {s : Locals} {ptr : Nat} {p : UInt64}
    {slots : List LeanExe.Pipeline.Slot} {rest : Program} {Q : Assertion Unit}
    (hRaw : RecordStorage shape heap store p) (hHeap : heap.At store)
    (hPtr : s.get ptr = some (.i64 p)) (hLength : slots.length = shape.fields.length)
    (hMask : maskOf slots = shape.mask) (hSlots : SlotsOwned heap store p 0 slots)
    (hApart : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint)
    (hNext : ∀ store',
      Memory.WritesRange store store' (p.toNat - 40) p.toNat → heap.At store' →
      NodeOwned heap store' p (.record slots) →
      Node.blocks store' p (.record slots) = Node.blocks store p (.record slots) →
      wp m rest Q store' s host) :
    wp m (restoreRecordCode shape ptr ++ rest) Q store s host := by
  obtain ⟨hWrites, hAt, hOwned, hBlocks, _⟩ := hRaw.restore hHeap hLength hMask hSlots hApart
  exact wp_restoreRecord hRaw hHeap hPtr (hNext _ hWrites hAt hOwned hBlocks)

#print axioms wp_restoreOwnedRecord

end Verified
