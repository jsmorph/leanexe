import Project.EulerRiemann.ExecutionRelease
import Project.Runtime.FreeList
import Project.ProofKit.MemoryRoundtrip

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.Memory

theorem releasedStore_bytes (store : Store Unit) (root head releases frees : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296) (address : Nat)
    (hOutside : address < root.toNat - 48 ∨ root.toNat ≤ address) :
    (releasedStore store root head releases frees).mem.bytes address = store.mem.bytes address := by
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have h40 : (40 : UInt64).toNat = 40 := rfl
  have hAddress (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (root - offset).toUInt32.toNat = root.toNat - offset.toNat := by
    rw [UInt64.toNat_toUInt32, toNat_sub_of_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold releasedStore
  dsimp only
  rw [write64_bytes_outside _ _ _ (by rw [hAddress 8 (by decide) (by decide)]; omega),
    write64_bytes_outside _ _ _ (by rw [hAddress 40 (by decide) (by decide)]; omega)]

theorem gridAt_releasedStore (store : Store Unit) (root head releases frees source : UInt64)
    (grid : Array Traversal.Cell) (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296)
    (hGrid : Memory.GridAt store source grid)
    (hSep : source.toNat + 8 * (7 * grid.size + 1) ≤ root.toNat - 48 ∨ root.toNat ≤ source.toNat) :
    Memory.GridAt (releasedStore store root head releases frees) source grid := by
  apply hGrid.frame
  · rw [releasedStore_pages]
  · intro address hLow hHigh
    exact releasedStore_bytes store root head releases frees hRoot hRoot32 address (by omega)

theorem freeListAt_releasedStore (store : Store Unit) (root capacity releases frees : UInt64)
    (nodes : List FreeNode) (hRoot : 48 ≤ root.toNat)
    (hRoot32 : root.toNat + capacity.toNat < 4294967296)
    (hFit : root.toNat + capacity.toNat ≤ store.mem.pages * 65536)
    (hCapacity : store.mem.read64 (root - 32).toUInt32 = capacity)
    (hList : FreeListAt store.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint ({ root, capacity } : FreeNode).region node.region) :
    FreeListAt (releasedStore store root (freeHead nodes) releases frees).mem
      ({ root, capacity } :: nodes) := by
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have h32 : (32 : UInt64).toNat = 32 := rfl
  have h40 : (40 : UInt64).toNat = 40 := rfl
  have hList40 := hList.frame_write64_disjoint (writer := { root, capacity })
    (writeOffset := 40) (value := 0) hRoot hRoot32 (by decide) (by decide) hSep
  have hList8 := hList40.frame_write64_disjoint (writer := { root, capacity })
    (writeOffset := 8) (value := freeHead nodes) hRoot hRoot32 (by decide) (by decide) hSep
  have hAddress (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (root - offset).toUInt32.toNat = root.toNat - offset.toNat := by
    rw [UInt64.toNat_toUInt32, toNat_sub_of_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
  change FreeListAt ((store.mem.write64 (root - 40).toUInt32 0).write64
    (root - 8).toUInt32 (freeHead nodes)) ({ root, capacity } :: nodes)
  refine .cons hRoot hRoot32 hFit ?_ ?_ ?_ hSep hList8
  · change ((store.mem.write64 (root - 40).toUInt32 0).write64
      (root - 8).toUInt32 (freeHead nodes)).read64 (root - 40).toUInt32 = 0
    rw [read64_write64_disjoint _ _ _ _ (by
      rw [hAddress 8 (by decide) (by decide), hAddress 40 (by decide) (by decide)]
      omega)]
    exact read64_write64 ..
  · change ((store.mem.write64 (root - 40).toUInt32 0).write64
      (root - 8).toUInt32 (freeHead nodes)).read64 (root - 32).toUInt32 = capacity
    rw [read64_write64_disjoint _ _ _ _ (by
      rw [hAddress 8 (by decide) (by decide), hAddress 32 (by decide) (by decide)]
      omega)]
    rw [read64_write64_disjoint _ _ _ _ (by
      rw [hAddress 40 (by decide) (by decide), hAddress 32 (by decide) (by decide)]
      omega)]
    exact hCapacity
  · exact read64_write64 ..

#print axioms releasedStore_bytes
#print axioms gridAt_releasedStore
#print axioms freeListAt_releasedStore

end Project.EulerRiemann.Execution
