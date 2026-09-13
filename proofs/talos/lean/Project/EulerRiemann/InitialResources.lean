import Project.EulerRiemann.InitialHeapBounds
import Project.EulerRiemann.RetryResources

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

theorem initial_allocation_cap (store : Store Unit) (heap : Heap)
    (count : Nat) (hCount : count ≤ 1048576)
    (hFit : heap.top.toNat + 48 + initialBytes count ≤ store.memoryCap module 0 * 65536) :
    FixedArrayBump.requiredPages heap.top (normalizedCapacity (UInt64.ofNat count) 7) ≤
      store.memoryCap module 0 := by
  unfold FixedArrayBump.requiredPages
  rw [initial_requested_bytes count hCount]
  omega

theorem RetryStoreAt.initialAllocated {initial current final : Store Unit} {initialHeap heap : Heap}
    (h : RetryStoreAt initial initialHeap current heap) (count : Nat) (hCount : count ≤ 1048576)
    (hBelow : InitialFreeBelow count heap.nodes)
    (hFit : heap.top.toNat + 48 + initialBytes count < 4294967296)
    (hHeap : (heap.allocate (normalizedCapacity (UInt64.ofNat count) 7)).At final)
    (hWrites : Memory.WritesGrid (heap.allocateStore current (normalizedCapacity (UInt64.ofNat count) 7))
      final (heap.top + 48) count) :
    RetryStoreAt initial initialHeap final (heap.allocate (normalizedCapacity (UInt64.ofNat count) 7)) ∧
      ∀ (saved : FreeNode) (grid : Array Traversal.Cell), initialHeap.Owns initial saved grid →
        regionsDisjoint saved.region
          (allocatedNode heap.top (normalizedCapacity (UInt64.ofNat count) 7) heap.nodes).region := by
  let need := normalizedCapacity (UInt64.ofNat count) 7
  have hNeed : need.toNat = initialBytes count := initial_requested_bytes count hCount
  have hNone : takeFirstFitFrom 0 need heap.nodes = none := initial_no_fit count hCount heap.nodes hBelow
  have hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := by
    intro _
    rw [hNeed]
    exact hFit.le
  have hCap : final.memoryCap module 0 = current.memoryCap module 0 := by
    rw [hWrites.1]
    change (heap.allocateStore current need).memoryCap module 0 = current.memoryCap module 0
    exact heap.allocateStore_memoryCap current need module 0
  apply h.after_step hHeap
    (initial_allocated_pages heap current final count 65536 hCount h.pages (by omega) hWrites)
    hCap (allocatedNode heap.top need heap.nodes)
  intro saved grid hSaved
  refine ⟨hSaved.swept need count h.heapState ?_ hBump ?_, ?_⟩
  · rw [hNeed]
    simp only [initialBytes]
    omega
  · simpa only [allocatedRoot, hNone] using hWrites
  · exact allocated_region_disjoint heap.top need saved heap.nodes hSaved.buffer.rootBound
      hSaved.separated hSaved.below hBump

#print axioms initial_allocation_cap
#print axioms RetryStoreAt.initialAllocated

end Project.EulerRiemann.Execution
