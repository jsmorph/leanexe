import Project.EulerRiemann.MemoryFrame
import Project.EulerRiemann.MemoryLength
import Project.EulerRiemann.AllocationPreserve

namespace Project.EulerRiemann.Memory
open Wasm Project.Runtime Project.Clob Project.ProofKit.Memory

theorem writeLength_frame (store : Store Unit) (ptr : UInt64) (size : Nat)
    (hFit : ptr.toNat + 8 ≤ 4294967296) :
    WritesGrid store (Project.ProofKit.FixedArrayResult.writeLength store ptr (UInt64.ofNat size))
      ptr size := by
  refine ⟨rfl, rfl, ?_⟩
  intro address hOutside
  apply write64_bytes_outside
  rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  omega

theorem WritesGrid.fresh {initial final : Store Unit} {ptr capacity stride : UInt64} {size : Nat}
    (hWrites : WritesGrid initial final ptr size)
    (hRoot : 48 ≤ ptr.toNat) (hRoot32 : ptr.toNat < 4294967296)
    (hFresh : FreshFixedArrayAt initial ptr capacity stride) :
    FreshFixedArrayAt final ptr capacity stride := by
  exact hFresh.frame hRoot32 hRoot (Nat.le_refl ptr.toNat)
    (fun address hBefore => hWrites.2.2 address (Or.inl hBefore))

theorem WritesGrid.fresh_disjoint {initial final : Store Unit}
    {source capacity stride target : UInt64} {size : Nat}
    (hWrites : WritesGrid initial final target size)
    (hRoot : 48 ≤ source.toNat) (hRoot32 : source.toNat < 4294967296)
    (hFresh : FreshFixedArrayAt initial source capacity stride)
    (hSep : source.toNat + capacity.toNat ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.toNat - 48) :
    FreshFixedArrayAt final source capacity stride := by
  apply hFresh.frame_region hRoot32 hRoot
  intro address hLow hHigh
  exact hWrites.2.2 address (by omega)

theorem WritesGrid.freeList {initial final : Store Unit} {ptr : UInt64} {size : Nat}
    {nodes : List FreeNode} (hWrites : WritesGrid initial final ptr size)
    (hList : FreeListAt initial.mem nodes)
    (hSep : Execution.gridFreeSeparated ptr size nodes) : FreeListAt final.mem nodes := by
  apply Project.ProofKit.FreeListMemory.frame_headers hList (Nat.le_of_eq hWrites.2.1.symm)
  intro node hNode address hLow hHigh
  have hDisjoint := hSep node hNode
  exact hWrites.2.2 address (by omega)

theorem WritesGrid.grid {initial final : Store Unit} {source target : UInt64} {size : Nat}
    {grid : Array Traversal.Cell} (hWrites : WritesGrid initial final target size)
    (hGrid : GridAt initial source grid)
    (hSep : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.toNat) : GridAt final source grid := by
  apply hGrid.frame (Nat.le_of_eq hWrites.2.1.symm)
  intro address hLow hHigh
  exact hWrites.2.2 address (by omega)

theorem WritesGrid.globals {initial final : Store Unit} {ptr : UInt64} {size : Nat}
    (hWrites : WritesGrid initial final ptr size) : final.globals = initial.globals := by
  rw [hWrites.1]

theorem WritesGrid.memoryCap {initial final : Store Unit} {ptr : UInt64} {size : Nat}
    (hWrites : WritesGrid initial final ptr size) (m : Wasm.Module) (index : Nat) :
    final.memoryCap m index = initial.memoryCap m index := by
  rw [hWrites.1]
  rfl

#print axioms writeLength_frame
#print axioms WritesGrid.fresh
#print axioms WritesGrid.fresh_disjoint
#print axioms WritesGrid.freeList
#print axioms WritesGrid.grid
#print axioms WritesGrid.globals
#print axioms WritesGrid.memoryCap

end Project.EulerRiemann.Memory
