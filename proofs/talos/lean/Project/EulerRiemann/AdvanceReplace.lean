import Project.EulerRiemann.AdvanceResources

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem AdvanceCurrent.replace {initial current final : Store Unit} {initialHeap heap finalHeap : Heap}
    {n : Nat} {startTime time : UInt64} {source : FreeNode} {grid : Array Traversal.Cell} {tracked : Bool}
    (hCurrent : AdvanceCurrent initial initialHeap n startTime time current heap source grid tracked)
    (hStore : RetryStoreAt initial initialHeap current heap)
    (hTrial : RetryStoreAt current heap final finalHeap)
    (result : FreeNode) (resultGrid : Array Traversal.Cell) (nextTime : UInt64) (spare limit : Nat)
    (hIndexed : Traversal.Indexed n resultGrid) (hOwner : finalHeap.Owns final result resultGrid)
    (hCapacity : gridCapacity n ≤ result.capacity)
    (hSeparated : ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns current saved savedGrid →
      regionsDisjoint saved.region result.region)
    (hReserve : finalHeap.Reserved (gridCapacity n) (spare + if tracked then 1 else 2) limit) :
    let nextStore := if tracked then finalHeap.releaseStore final source else final
    let nextHeap := if tracked then finalHeap.release source else finalHeap
    RetryStoreAt initial initialHeap nextStore nextHeap ∧
    AdvanceCurrent initial initialHeap n startTime nextTime nextStore nextHeap result resultGrid true ∧
    nextHeap.Reserved (gridCapacity n) (spare + 2) limit := by
  have hPreserved := hStore.trans hTrial
  have hOld := hTrial.held source grid hCurrent.owner
  have hSepOldNew := hSeparated source grid hCurrent.owner
  have hSepOriginal (saved : FreeNode) (savedGrid : Array Traversal.Cell)
      (hSaved : initialHeap.Owns initial saved savedGrid) : regionsDisjoint saved.region result.region :=
    hSeparated saved savedGrid (hStore.held saved savedGrid hSaved)
  have hReserved := advance_reserved_after_replace finalHeap source n spare limit tracked hCurrent.capacity hReserve
  cases tracked with
  | false =>
    refine ⟨hPreserved, ⟨hIndexed, hOwner, hCapacity, ?_⟩, hReserved⟩
    simpa [AdvanceOrigin] using hSepOriginal
  | true =>
    have hRoot := hOld.buffer.rootBound
    have hRoot32 : source.root.toNat ≤ 4294967296 := by
      have := hOld.buffer.addressBound
      omega
    have hOrigin : ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell),
        initialHeap.Owns initial saved savedGrid → regionsDisjoint saved.region source.region := by
      simpa [AdvanceOrigin] using hCurrent.origin
    have hNextStore := hPreserved.released source grid hOld hOrigin
    have hNextOwner := hOwner.released source hRoot hRoot32 (regionsDisjoint_symm hSepOldNew)
    refine ⟨hNextStore, ⟨hIndexed, hNextOwner, hCapacity, ?_⟩, hReserved⟩
    simpa [AdvanceOrigin] using hSepOriginal

#print axioms AdvanceCurrent.replace

end Project.EulerRiemann.Execution
