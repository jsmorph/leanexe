import Project.EulerRiemann.RetryInvariant

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem RetryStoreAt.after_step {initial current final : Store Unit}
    {initialHeap heap finalHeap : Heap}
    (h : RetryStoreAt initial initialHeap current heap)
    (hHeap : finalHeap.At final) (hPages : final.mem.pages ≤ 65536)
    (hCap : final.memoryCap Project.EulerRiemann.«module» 0 = current.memoryCap Project.EulerRiemann.«module» 0)
    (result : FreeNode)
    (hFrame : ∀ (saved : FreeNode) (grid : Array Traversal.Cell), heap.Owns current saved grid →
      finalHeap.Owns final saved grid ∧ regionsDisjoint saved.region result.region) :
    RetryStoreAt initial initialHeap final finalHeap ∧
      ∀ (saved : FreeNode) (grid : Array Traversal.Cell), initialHeap.Owns initial saved grid →
        regionsDisjoint saved.region result.region := by
  exact ⟨⟨hHeap, hPages, hCap.trans h.cap,
    fun saved grid hSaved => (hFrame saved grid (h.held saved grid hSaved)).1⟩,
    fun saved grid hSaved => (hFrame saved grid (h.held saved grid hSaved)).2⟩

theorem RetryStoreAt.released {initial current : Store Unit} {initialHeap heap : Heap}
    (h : RetryStoreAt initial initialHeap current heap) (result : FreeNode)
    (grid : Array Traversal.Cell) (hOwner : heap.Owns current result grid)
    (hSep : ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), initialHeap.Owns initial saved savedGrid →
      regionsDisjoint saved.region result.region) :
    RetryStoreAt initial initialHeap (heap.releaseStore current result) (heap.release result) := by
  have hRoot := hOwner.buffer.rootBound
  have hRoot32 : result.root.toNat ≤ 4294967296 := by
    have := hOwner.buffer.addressBound
    omega
  refine ⟨heap.release_at current result h.heapState hRoot hOwner.buffer.addressBound
    hOwner.buffer.memoryBound hOwner.buffer.fresh.2.2.1 hOwner.below hOwner.separated, ?_, ?_, ?_⟩
  · simpa only [Heap.releaseStore, releasedStore_pages] using h.pages
  · simpa only [Heap.releaseStore, releasedStore_memoryCap] using h.cap
  · intro saved savedGrid hSaved
    exact (h.held saved savedGrid hSaved).released result hRoot hRoot32 (hSep saved savedGrid hSaved)

#print axioms RetryStoreAt.after_step
#print axioms RetryStoreAt.released

end Project.EulerRiemann.Execution
