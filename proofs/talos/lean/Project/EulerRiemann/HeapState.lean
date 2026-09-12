import Project.EulerRiemann.AllocationGlobals
import Project.EulerRiemann.ReleaseMemory

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit

structure Heap where
  top : UInt64
  nodes : List FreeNode
  allocations : UInt64
  retains : UInt64
  releases : UInt64
  frees : UInt64

def Heap.globals (heap : Heap) : List Wasm.Value :=
  [.i64 heap.top, .i64 (freeHead heap.nodes), .i64 heap.allocations,
    .i64 heap.retains, .i64 heap.releases, .i64 heap.frees]

structure Heap.At (heap : Heap) (store : Store Unit) : Prop where
  globals : store.globals.globals = heap.globals
  freeList : FreeListAt store.mem heap.nodes
  below : ∀ node ∈ heap.nodes, node.root.toNat + node.capacity.toNat ≤ heap.top.toNat

def Heap.allocate (heap : Heap) (need : UInt64) : Heap :=
  { heap with
    top := allocatedTop heap.top need heap.nodes
    nodes := allocatedNodes need heap.nodes
    allocations := heap.allocations + 1 }

def Heap.allocateStore (heap : Heap) (store : Store Unit) (need : UInt64) : Store Unit :=
  countedStore (allocatedStore store heap.top need heap.nodes) heap.allocations

def Heap.release (heap : Heap) (node : FreeNode) : Heap :=
  { heap with nodes := node :: heap.nodes, releases := heap.releases + 1, frees := heap.frees + 1 }

def Heap.releaseStore (heap : Heap) (store : Store Unit) (node : FreeNode) : Store Unit :=
  releasedStore store node.root (freeHead heap.nodes) heap.releases heap.frees

theorem Heap.allocate_globals (heap : Heap) (store : Store Unit) (need : UInt64)
    (hHeap : heap.At store) :
    (heap.allocateStore store need).globals.globals = (heap.allocate need).globals := by
  cases hTake : takeFirstFitFrom 0 need heap.nodes with
  | some choice =>
    have hHead := Project.ProofKit.FreeListMemory.remaining_head hHeap.freeList hTake
    simp only [Heap.allocateStore, Heap.allocate, countedStore, allocatedStore, allocatedTop,
      allocatedNodes, hTake, fixedArrayAllocFitStore]
    split <;> simp_all [Heap.globals, hHeap.globals]
  | none =>
    simp only [Heap.allocateStore, Heap.allocate, countedStore, allocatedStore, allocatedTop,
      allocatedNodes, hTake, bumpStore_globals, hHeap.globals]
    rfl

theorem Heap.allocate_at (heap : Heap) (store : Store Unit) (need : UInt64)
    (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).At (heap.allocateStore store need) := by
  refine ⟨heap.allocate_globals store need hHeap, ?_, ?_⟩
  · exact freeListAt_allocated store heap.top need heap.nodes hHeap.freeList hHeap.below hBump
  · exact (allocated_below_top heap.top need heap.nodes hHeap.below hBump).2

theorem Heap.release_at (heap : Heap) (store : Store Unit) (node : FreeNode)
    (hHeap : heap.At store) (hRoot : 48 ≤ node.root.toNat)
    (hBound : node.root.toNat + node.capacity.toNat < 4294967296)
    (hFit : node.root.toNat + node.capacity.toNat ≤ store.mem.pages * 65536)
    (hCapacity : store.mem.read64 (node.root - 32).toUInt32 = node.capacity)
    (hBelow : node.root.toNat + node.capacity.toNat ≤ heap.top.toNat)
    (hSep : ∀ other ∈ heap.nodes, regionsDisjoint node.region other.region) :
    (heap.release node).At (heap.releaseStore store node) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Heap.releaseStore, releasedStore, Heap.release, Heap.globals, hHeap.globals,
      Heap.globals, freeHead, List.set]
  · exact freeListAt_releasedStore store node.root node.capacity heap.releases heap.frees
      heap.nodes hRoot hBound hFit hCapacity hHeap.freeList hSep
  · intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact hBelow
    · exact hHeap.below other hOther

theorem Heap.allocateStore_memoryCap (heap : Heap) (store : Store Unit) (need : UInt64)
    (m : Wasm.Module) (index : Nat) :
    (heap.allocateStore store need).memoryCap m index = store.memoryCap m index :=
  allocatedStore_memoryCap store heap.top need heap.nodes m index

#print axioms Heap.allocate_globals
#print axioms Heap.allocate_at
#print axioms Heap.release_at
#print axioms Heap.allocateStore_memoryCap

end Project.EulerRiemann.Execution
