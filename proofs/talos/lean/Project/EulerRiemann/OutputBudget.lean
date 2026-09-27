import Project.EulerRiemann.WordAllocationBounds
import Project.EulerRiemann.OutputMapPrepare

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

structure OutputBudget (store : Store Unit) (heap : Heap) (remaining pageLimit : Nat) (module_ : Wasm.Module := module) : Prop where
  addressBound : heap.top.toNat + remaining < 4294967296
  heapPages : heap.top.toNat + remaining ≤ pageLimit * 65536
  pages : store.mem.pages ≤ pageLimit
  pageLimitBound : pageLimit ≤ 65536
  memoryCap : pageLimit ≤ store.memoryCap module_ 0

theorem OutputBudget.mono {module_ : Wasm.Module} {store : Store Unit} {heap : Heap}
    {remaining smaller pageLimit : Nat} (h : OutputBudget store heap remaining pageLimit module_)
    (hSmaller : smaller ≤ remaining) : OutputBudget store heap smaller pageLimit module_ :=
  ⟨lt_of_le_of_lt (Nat.add_le_add_left hSmaller _) h.addressBound,
    (Nat.add_le_add_left hSmaller _).trans h.heapPages, h.pages, h.pageLimitBound, h.memoryCap⟩

theorem OutputBudget.transfer {source target : Wasm.Module} {store : Store Unit} {heap : Heap}
    {remaining pageLimit : Nat} (h : OutputBudget store heap remaining pageLimit source)
    (hCap : store.memoryCap target 0 = store.memoryCap source 0) :
    OutputBudget store heap remaining pageLimit target :=
  ⟨h.addressBound, h.heapPages, h.pages, h.pageLimitBound, hCap.symm ▸ h.memoryCap⟩

theorem OutputBudget.bump {module_ : Wasm.Module} {store : Store Unit} {heap : Heap} {remaining pageLimit : Nat}
    (h : OutputBudget store heap remaining pageLimit module_) (need : UInt64)
    (hCost : 48 + need.toNat ≤ remaining) :
    takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module_ 0 := by
  intro _
  have hAddress := h.addressBound
  have hPages := h.heapPages
  have hCap := h.memoryCap
  constructor
  · omega
  · unfold bumpPages
    omega

theorem OutputBudget.allocated {module_ : Wasm.Module} {store final : Store Unit} {heap : Heap} {remaining pageLimit start stop : Nat}
    (h : OutputBudget store heap remaining pageLimit module_) (need stride : UInt64) (remainingAfter : Nat)
    (hCost : 48 + need.toNat + remainingAfter ≤ remaining)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocateArrayStore store need stride) final start stop) :
    OutputBudget final (heap.allocate need) remainingAfter pageLimit module_ := by
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun hNone => ((h.bump need (by omega)) hNone).1.le
  have hTopEq := allocatedTop_toNat heap.top need heap.nodes hFit
  have hTop : (heap.allocate need).top.toNat ≤ heap.top.toNat + 48 + need.toNat := by
    change (allocatedTop heap.top need heap.nodes).toNat ≤ _
    rw [hTopEq]
    split <;> omega
  have hAddress := h.addressBound
  have hHeapPages := h.heapPages
  refine ⟨by omega, by omega, ?_, h.pageLimitBound, ?_⟩
  · rw [hWrites.2.1]
    exact heap.allocateArrayStore_pages_bound store need stride pageLimit h.pages (by intro _; omega)
  · rw [hWrites.1]
    change pageLimit ≤ (heap.allocateArrayStore store need stride).memoryCap module_ 0
    rw [heap.allocateArrayStore_memoryCap]
    exact h.memoryCap

theorem OutputBudget.released {module_ : Wasm.Module} {store : Store Unit} {heap : Heap} {remaining pageLimit : Nat}
    (h : OutputBudget store heap remaining pageLimit module_) (node : FreeNode) :
    OutputBudget (heap.releaseStore store node) (heap.release node) remaining pageLimit module_ :=
  ⟨h.addressBound, h.heapPages, h.pages, h.pageLimitBound, h.memoryCap⟩

theorem Heap.OwnsWords.allocation_disjoint {heap : Heap} {store : Store Unit} {source : FreeNode}
    {words : Array UInt64} (h : heap.OwnsWords store source words) (need : UInt64)
    (hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    regionsDisjoint source.region (allocatedNode heap.top need heap.nodes).region :=
  allocated_region_disjoint heap.top need source heap.nodes h.buffer.rootBound h.separated h.below hFit

def outputBytes (size : Nat) : Nat := 48 * size + 344

theorem output_bytes_allocations (size : Nat) : outputBytes size =
    (48 + 8 * (size + 1)) + (48 + 8 * (size + 1)) +
      (48 + 8 * (size + size + 1)) + (48 + 40) + (48 + 8 * (4 + (size + size) + 1)) := by
  unfold outputBytes
  omega

theorem output_bytes_bound (size : Nat) (hSize : size ≤ 640000) :
    outputBytes size ≤ 30720344 := by
  unfold outputBytes
  omega

#print axioms OutputBudget.bump
#print axioms OutputBudget.mono
#print axioms OutputBudget.transfer
#print axioms OutputBudget.allocated
#print axioms OutputBudget.released
#print axioms Heap.OwnsWords.allocation_disjoint
#print axioms output_bytes_allocations
#print axioms output_bytes_bound

end Project.EulerRiemann.Execution
