import Project.EulerRiemann.HeapAllocateExecute
import Project.EulerRiemann.AllocationPageBound

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob Project.ClobMatchFuel.BookAllocFit Project.ProofKit

def Heap.allocateArrayStore (heap : Heap) (store : Store Unit) (need stride : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted (FixedArrayAllocate.allocated store heap.top need stride heap.nodes)
    heap.allocations

theorem arrayAllocated_pages (store : Store Unit) (base need stride : UInt64) (nodes : List FreeNode) :
    (FixedArrayAllocate.allocated store base need stride nodes).mem.pages =
      (allocatedStore store base need nodes).mem.pages := by
  cases hTake : takeFirstFitFrom 0 need nodes <;>
    simp only [FixedArrayAllocate.allocated, allocatedStore, hTake] <;> rfl

theorem arrayAllocated_globals (store : Store Unit) (base need stride : UInt64) (nodes : List FreeNode) :
    (FixedArrayAllocate.allocated store base need stride nodes).globals =
      (allocatedStore store base need nodes).globals := by
  cases hTake : takeFirstFitFrom 0 need nodes <;>
    simp only [FixedArrayAllocate.allocated, allocatedStore, hTake] <;> rfl

theorem arrayBump_bytes_outside (store : Store Unit) (base need stride : UInt64)
    (hFit : base.toNat + 48 + need.toNat ≤ 4294967296) (address : Nat)
    (hOutside : address < base.toNat ∨ base.toNat + 48 ≤ address) :
    (FixedArrayBump.allocated store base need stride).mem.bytes address = store.mem.bytes address := by
  change (fixedArrayHeaderMem (MemoryGrowth.ensured store (bumpPages base need)).mem base need stride).bytes
    address = store.mem.bytes address
  rw [FixedArrayHeader.bytes_outside _ base need stride (by omega) address hOutside,
    MemoryGrowth.ensured_bytes]

theorem arrayAllocated_freeList (store : Store Unit) (base need stride : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreeListAt (FixedArrayAllocate.allocated store base need stride nodes).mem (allocatedNodes need nodes) := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [FixedArrayAllocate.allocated, allocatedNodes, hTake, fixedArrayAllocFitStore] using
      freeListAt_fixedArrayAllocFitMem stride hList hTake
  | none =>
    have hPages : store.mem.pages ≤ (FixedArrayBump.allocated store base need stride).mem.pages := by
      have hGeneral := (allocated_pages_ge store base need nodes).trans_eq
        (arrayAllocated_pages store base need stride nodes).symm
      simpa only [FixedArrayAllocate.allocated, hTake] using hGeneral
    simp only [FixedArrayAllocate.allocated, allocatedNodes, hTake]
    apply FreeListMemory.frame_headers hList hPages
    intro node hNode address _ hHigh
    have hEnd := hBelow node hNode
    exact arrayBump_bytes_outside store base need stride (hBump hTake) address (Or.inl (by omega))

theorem arrayAllocated_fresh (store : Store Unit) (base need stride : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreshFixedArrayAt (FixedArrayAllocate.allocated store base need stride nodes)
      (allocatedRoot base need nodes) (allocatedCapacity need nodes) stride := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [FixedArrayAllocate.allocated, allocatedRoot, allocatedCapacity, hTake] using
      freshFixedArrayAt_fixedArrayAllocFitStore stride hList hTake
  | none =>
    simp only [FixedArrayAllocate.allocated, allocatedRoot, allocatedCapacity, hTake]
    exact FixedArrayHeader.fresh (MemoryGrowth.ensured store (bumpPages base need))
      base need stride (by have := hBump hTake; omega)

theorem Heap.allocateArrayStore_at (heap : Heap) (store : Store Unit) (need stride : UInt64)
    (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).At (heap.allocateArrayStore store need stride) := by
  refine ⟨?_, arrayAllocated_freeList store heap.top need stride heap.nodes
    hHeap.freeList hHeap.below hBump, (allocated_below_top heap.top need heap.nodes hHeap.below hBump).2⟩
  simpa only [Heap.allocateArrayStore, FixedArrayAllocateNone.counted, arrayAllocated_globals,
    Heap.allocateStore, countedStore] using heap.allocate_globals store need hHeap

theorem Heap.allocateArrayStore_pages_bound (heap : Heap) (store : Store Unit)
    (need stride : UInt64) (pageLimit : Nat) (hPages : store.mem.pages ≤ pageLimit)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ pageLimit * 65536) :
    (heap.allocateArrayStore store need stride).mem.pages ≤ pageLimit := by
  change (FixedArrayAllocate.allocated store heap.top need stride heap.nodes).mem.pages ≤ pageLimit
  rw [arrayAllocated_pages]
  exact allocated_pages_bound store heap.top need heap.nodes pageLimit hPages hBump

theorem Heap.allocateArrayStore_memoryCap (heap : Heap) (store : Store Unit)
    (need stride : UInt64) (m : Wasm.Module) (index : Nat) :
    (heap.allocateArrayStore store need stride).memoryCap m index = store.memoryCap m index := by
  change (FixedArrayAllocate.allocated store heap.top need stride heap.nodes).memoryCap m index = _
  unfold FixedArrayAllocate.allocated
  split
  · rfl
  · unfold FixedArrayBump.allocated MemoryGrowth.ensured
    split <;> rfl

#print axioms arrayAllocated_pages
#print axioms arrayAllocated_globals
#print axioms arrayBump_bytes_outside
#print axioms arrayAllocated_freeList
#print axioms arrayAllocated_fresh
#print axioms Heap.allocateArrayStore_at
#print axioms Heap.allocateArrayStore_pages_bound
#print axioms Heap.allocateArrayStore_memoryCap

end Project.EulerRiemann.Execution
