import Project.EulerRiemann.AdvanceInvariant

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem RetryStoreAt.trans {initial current final : Store Unit} {initialHeap heap finalHeap : Heap}
    (h : RetryStoreAt initial initialHeap current heap) (hNext : RetryStoreAt current heap final finalHeap) :
    RetryStoreAt initial initialHeap final finalHeap :=
  ⟨hNext.heapState, hNext.pages, hNext.cap.trans h.cap,
    fun saved grid hSaved => hNext.held saved grid (h.held saved grid hSaved)⟩

theorem freeNode_roots_ne (left right : FreeNode) (h : regionsDisjoint left.region right.region) :
    left.root ≠ right.root := by
  intro hRoot
  simp only [regionsDisjoint, FreeNode.region] at h
  rw [hRoot] at h
  omega

theorem advance_reserved_after_replace (heap : Heap) (source : FreeNode) (n spare limit : Nat)
    (tracked : Bool) (hCapacity : gridCapacity n ≤ source.capacity)
    (hReserve : heap.Reserved (gridCapacity n) (spare + if tracked then 1 else 2) limit) :
    (if tracked then heap.release source else heap).Reserved (gridCapacity n) (spare + 2) limit := by
  cases tracked with
  | false => simpa using hReserve
  | true => simpa using hReserve.release source hCapacity

#print axioms RetryStoreAt.trans
#print axioms freeNode_roots_ne
#print axioms advance_reserved_after_replace

end Project.EulerRiemann.Execution
