import Project.EulerRiemann.FrozenRetryResources
import Project.EulerRiemann.FrozenHeapEmpty
import Project.EulerRiemann.FrozenHeapReserveSmall
import Project.EulerRiemann.FrozenAllocationPageBound

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayResult

theorem RetryStoreAt.empty {initial current : Store Unit} {initialHeap heap : Heap}
    (h : RetryStoreAt initial initialHeap current heap) (need : UInt64) (spare limit : Nat)
    (hReserved : heap.Reserved need (spare + 2) limit) (hNeed : 8 ≤ need)
    (hLimit : limit < 4294967296) :
    RetryStoreAt initial initialHeap (heap.emptyStore current) (heap.allocate 8) ∧
      (heap.allocate 8).Owns (heap.emptyStore current) (allocatedNode heap.top 8 heap.nodes) #[] ∧
      (heap.allocate 8).Reserved need (spare + 1) limit ∧
      ∀ (saved : FreeNode) (grid : Array Traversal.Cell), initialHeap.Owns initial saved grid →
        regionsDisjoint saved.region (allocatedNode heap.top 8 heap.nodes).region := by
  have hBump : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 < 4294967296 :=
    fun hNone => (hReserved.bump_small_bound (by omega) hNeed hNone).trans_lt hLimit
  have hOwned := heap.empty_owned current h.heapState hBump
  have hPages : (heap.emptyStore current).mem.pages ≤ 65536 := by
    simpa only [Heap.emptyStore, writeLength_pages, Heap.allocateStore, countedStore] using
      allocated_pages_le current heap.top 8 heap.nodes h.pages (fun hNone => (hBump hNone).le)
  have hCap : (heap.emptyStore current).memoryCap module 0 = current.memoryCap module 0 := by
    change (heap.allocateStore current 8).memoryCap module 0 = current.memoryCap module 0
    exact heap.allocateStore_memoryCap current 8 module 0
  have hState := h.after_step hOwned.1 hPages hCap (allocatedNode heap.top 8 heap.nodes) hOwned.2.2
  have hReserve := hReserved.allocate_small (by omega) hNeed hLimit.le
  exact ⟨hState.1, hOwned.2.1, by simpa using hReserve, hState.2⟩

theorem Heap.emptyStore_pages_bound (heap : Heap) (store : Store Unit)
    (need : UInt64) (spare limit pageLimit : Nat)
    (hPages : store.mem.pages ≤ pageLimit)
    (hReserved : heap.Reserved need (spare + 2) limit) (hNeed : 8 ≤ need)
    (hLimitPages : limit ≤ pageLimit * 65536) :
    (heap.emptyStore store).mem.pages ≤ pageLimit := by
  simp only [Heap.emptyStore, writeLength_pages]
  apply heap.allocateStore_pages_bound store 8 pageLimit hPages
  intro hNone
  exact (hReserved.bump_small_bound (by omega) hNeed hNone).trans hLimitPages

#print axioms RetryStoreAt.empty
#print axioms Heap.emptyStore_pages_bound

end Project.EulerRiemann.Frozen.Execution
