import Project.EulerRiemann.MemoryOwnership

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit.FixedArrayResult

def initialSingletonStore (store : Store Unit) (root : UInt64) (cell : Traversal.Cell) : Store Unit :=
  Memory.writeCell (writeLength store root 1) root 0 cell

theorem initial_singleton_grid (store : Store Unit) (root : UInt64) (cell : Traversal.Cell)
    (hFit32 : root.toNat + 64 ≤ 4294967296)
    (hFitMemory : root.toNat + 64 ≤ store.mem.pages * 65536) :
    Memory.GridAt (initialSingletonStore store root cell) root #[cell] := by
  have hPrefix := Memory.writeLength_prefix store root #[cell] hFit32 hFitMemory
  have hCell := hPrefix.write_cell (i := 0) (by simp)
  exact hCell.complete

theorem initial_singleton_writes (store : Store Unit) (root : UInt64) (cell : Traversal.Cell)
    (hFit32 : root.toNat + 64 ≤ 4294967296) :
    Memory.WritesGrid store (initialSingletonStore store root cell) root 1 :=
  (Memory.writeLength_frame store root 1 (by omega)).trans
    (Memory.writeCell_frame cell hFit32 (by decide))

#print axioms initial_singleton_grid
#print axioms initial_singleton_writes

end Project.EulerRiemann.Execution
