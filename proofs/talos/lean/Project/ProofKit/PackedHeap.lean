import Project.EulerRiemann.HeapFrame
import Project.ProofKit.PackedAllocationMemory

namespace Project.ProofKit.PackedAllocation
open Wasm Project.Runtime Project.EulerRiemann.Execution

theorem globals_eq (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) :
    (allocated store base need nodes).globals = (allocatedStore store base need nodes).globals := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [allocated, allocatedStore, hTake, PackedReuse.reused,
      FixedArrayReuse.unlinkStore, Project.ClobMatchFuel.BookAllocFit.fixedArrayAllocFitStore]
  | none => simp only [allocated, allocatedStore, hTake]; rfl

theorem pages_eq (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) :
    (allocated store base need nodes).mem.pages = (allocatedStore store base need nodes).mem.pages := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [allocated, allocatedStore, hTake, PackedReuse.reused_pages, fitStore_pages]
  | none => simp only [allocated, allocatedStore, hTake]; rfl

theorem memoryCap (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (module_ : Wasm.Module) (index : Nat) :
    (allocated store base need nodes).memoryCap module_ index = store.memoryCap module_ index := by
  unfold allocated
  split
  · rfl
  · unfold PackedAllocate.allocated FixedArrayBump.preparedStore MemoryGrowth.ensured
    split <;> rfl

theorem fresh (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 + need.toNat ≤ 4294967296) :
    PackedHeader.FreshAt (allocated store base need nodes).mem
      (allocatedRoot base need nodes) (allocatedCapacity need nodes) := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    obtain ⟨hRoot, hBound, _⟩ := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
    have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
      Memory.toNat_sub_of_le _ _ hRoot
    simpa only [allocated, allocatedRoot, allocatedCapacity, hTake, PackedReuse.reused,
      UInt64.sub_add_cancel] using
      PackedHeader.fresh (FixedArrayReuse.unlinkStore store choice).mem
        (choice.node.root - 48) choice.node.capacity (by rw [hBase]; omega)
  | none =>
    simpa only [allocated, allocatedRoot, allocatedCapacity, hTake, PackedAllocate.allocated] using
      PackedHeader.fresh (FixedArrayBump.preparedStore store base need).mem base need
        (by have := hBump hTake; omega)

end Project.ProofKit.PackedAllocation

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

def Heap.allocatePackedStore (heap : Heap) (store : Store Unit) (need : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted (PackedAllocation.allocated store heap.top need heap.nodes) heap.allocations

theorem Heap.allocatePacked_globals (heap : Heap) (store : Store Unit) (need : UInt64)
    (hHeap : heap.At store) :
    (heap.allocatePackedStore store need).globals.globals = (heap.allocate need).globals := by
  simpa only [Heap.allocatePackedStore, FixedArrayAllocateNone.counted,
    PackedAllocation.globals_eq, Heap.allocateStore, countedStore] using
    heap.allocate_globals store need hHeap

theorem Heap.allocatePacked_at (heap : Heap) (store : Store Unit) (need : UInt64)
    (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).At (heap.allocatePackedStore store need) := by
  refine ⟨heap.allocatePacked_globals store need hHeap, ?_, ?_⟩
  · exact PackedAllocation.freeListAt store heap.top need heap.nodes hHeap.freeList
      (fun h => by have := hBump h; omega) hHeap.below
  · exact (allocated_below_top heap.top need heap.nodes hHeap.below hBump).2

theorem Heap.packedWritten_at (heap : Heap) (initial final : Store Unit)
    (need : UInt64) (count : Nat) (hHeap : heap.At initial) (hNeed : count ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hWrites : Memory.WritesRange (heap.allocatePackedStore initial need) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + count)) :
    (heap.allocate need).At final := by
  refine ⟨?_, ?_, (heap.allocatePacked_at initial need hHeap hBump).below⟩
  · have hGlobals := congrArg (fun st : Store Unit => st.globals.globals) hWrites.1
    exact hGlobals.trans (heap.allocatePacked_globals initial need hHeap)
  · apply PackedAllocation.freeListAt_after_writes initial final heap.top need heap.allocations
      heap.nodes hHeap.freeList (fun h => by have := hBump h; omega) hHeap.below
    exact hWrites.mono (Nat.le_refl _) (Nat.add_le_add_left hNeed _)

theorem Heap.allocatePackedStore_memoryCap (heap : Heap) (store : Store Unit) (need : UInt64)
    (module_ : Wasm.Module) (index : Nat) :
    (heap.allocatePackedStore store need).memoryCap module_ index = store.memoryCap module_ index :=
  PackedAllocation.memoryCap store heap.top need heap.nodes module_ index

theorem Heap.allocatePackedStore_pages_le (heap : Heap) (store : Store Unit) (need : UInt64)
    (hPages : store.mem.pages ≤ 65536)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocatePackedStore store need).mem.pages ≤ 65536 := by
  change (PackedAllocation.allocated store heap.top need heap.nodes).mem.pages ≤ 65536
  rw [PackedAllocation.pages_eq]
  exact allocated_pages_le store heap.top need heap.nodes hPages hBump

theorem Heap.frame_allocatePacked (heap : Heap) (initial : Store Unit) (need : UInt64)
    (hHeap : heap.At initial)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    heap.Frame initial (heap.allocate need) (heap.allocatePackedStore initial need) := by
  refine ⟨PackedAllocation.allocated_pages initial heap.top need heap.nodes, ?_, ?_⟩
  · intro lo hi h
    refine ⟨?_, fun node hNode => h.separated node (allocatedNodes_mem need heap.nodes node hNode)⟩
    have hTop := allocatedTop_toNat heap.top need heap.nodes hBump
    change hi ≤ (allocatedTop heap.top need heap.nodes).toNat
    rw [hTop]
    split <;> have := h.below <;> omega
  · intro lo hi h address hLo hHi
    exact PackedAllocation.bytes_preserved initial heap.top need heap.nodes lo hi address
      hHeap.freeList (fun h => by have := hBump h; omega) h.below h.separated hLo hHi

theorem Heap.frame_packedWritten (heap : Heap) (initial final : Store Unit)
    (need : UInt64) (count : Nat) (hHeap : heap.At initial) (hNeed : count ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hWrites : Memory.WritesRange (heap.allocatePackedStore initial need) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + count)) :
    heap.Frame initial (heap.allocate need) final := by
  have hAlloc := heap.frame_allocatePacked initial need hHeap hBump
  refine ⟨hAlloc.pages.trans hWrites.2.1.ge, hAlloc.protects, ?_⟩
  intro lo hi h address hLo hHi
  have hSep := h.allocated_disjoint need hBump
  have hCapacity := allocated_capacity need heap.nodes
  exact (hWrites.2.2 address (by omega)).trans (hAlloc.bytes lo hi h address hLo hHi)

#print axioms Project.ProofKit.PackedAllocation.fresh
#print axioms Heap.allocatePacked_at
#print axioms Heap.packedWritten_at
#print axioms Heap.frame_packedWritten

end Project.EulerRiemann.Execution
