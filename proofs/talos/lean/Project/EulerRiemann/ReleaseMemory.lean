import Project.EulerRiemann.ExecutionRelease
import Project.Runtime.FreeList
import Project.ProofKit.MemoryRoundtrip

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.Memory

theorem releasedStore_bytes (store : Store Unit) (root head releases frees : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296) (address : Nat)
    (hOutside : address < root.toNat - 48 ∨ root.toNat ≤ address) :
    (releasedStore store root head releases frees).mem.bytes address = store.mem.bytes address :=
  Project.ProofKit.FixedArrayRelease.bytes_outside store root head releases frees
    hRoot hRoot32 address hOutside

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
      ({ root, capacity } :: nodes) :=
  Project.ProofKit.FixedArrayRelease.freeListAt store root capacity releases frees
    nodes hRoot hRoot32 hFit hCapacity hList hSep

#print axioms releasedStore_bytes
#print axioms gridAt_releasedStore
#print axioms freeListAt_releasedStore

end Project.EulerRiemann.Execution
