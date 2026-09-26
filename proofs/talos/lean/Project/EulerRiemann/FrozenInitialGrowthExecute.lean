import Project.EulerRiemann.FrozenInitialGrowthAllocate
import Project.EulerRiemann.FrozenInitialPrefix

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime

theorem initial_growth_spec (env : HostEnv Unit) (initial store : Store Unit)
    (initialHeap heap : Heap) (frame : Locals) (fuel : UInt64) (n size : Nat)
    (source : FreeNode) (tracked : Bool) (grid : Array Traversal.Cell) (limit pageLimit : Nat)
    (hFrame : InitialFrameAt frame fuel n size source.root (if tracked then source.root else 0) 0 false)
    (hScratch : InitialScratch frame) (hState : RetryStoreAt initial initialHeap store heap)
    (hOwner : heap.Owns store source grid) (hPrefix : InitialPrefix n grid.size grid)
    (hCount : grid.size + grid.size ≤ 1048576) (hPositive : 0 < grid.size) (hGrow : grid.size < size)
    (hBelow : InitialFreeBelow (min size grid.size) heap.nodes)
    (hCapacity : source.capacity.toNat = initialBytes grid.size)
    (hSeparated : tracked = true → ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell),
      initialHeap.Owns initial saved savedGrid → regionsDisjoint saved.region source.region)
    (hFuel : 0 < fuel.toNat)
    (hReserve : heap.top.toNat + initialRemainingBytes grid.size fuel.toNat size ≤ limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ store.memoryCap module 0 * 65536)
    (hPhysical : store.mem.pages ≤ pageLimit) (hPhysicalLimit : limit ≤ pageLimit * 65536)
    (hn : n ≤ 800) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final finalHeap resultFrame,
      RetryStoreAt initial initialHeap final finalHeap →
      finalHeap.Owns final (initialGrowthNode heap grid.size) (grid ++ initialMapOutput n grid.size grid) →
      InitialPrefix n (grid.size + grid.size) (grid ++ initialMapOutput n grid.size grid) →
      final.mem.pages ≤ pageLimit →
      InitialFreeBelow (min size (grid.size + grid.size)) finalHeap.nodes →
      finalHeap.top.toNat + initialRemainingBytes (grid.size + grid.size) (fuel.toNat - 1) size ≤ limit →
      (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), initialHeap.Owns initial saved savedGrid →
        regionsDisjoint saved.region (initialGrowthNode heap grid.size).region) →
      (initialGrowthNode heap grid.size).capacity.toNat = initialBytes (grid.size + grid.size) →
      InitialFrameAt resultFrame (fuel - 1) n size (initialGrowthNode heap grid.size).root
        (initialGrowthNode heap grid.size).root 0 false →
      InitialScratch resultFrame → wp module rest Q final resultFrame env) :
    wp module (initialGrowBody ++ rest) Q store frame env := by
  have hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + grid.size < 1048576 := by
    intro i hi
    rw [hPrefix.cell i hi, Traversal.initialCell_index]
    omega
  apply initial_growth_allocate_spec env initial store initialHeap heap frame fuel n size source
    (if tracked then source.root else 0) 0 false grid limit pageLimit hFrame hScratch hState hOwner
    hCount hBelow hFuel hReserve hLimit hCap hPhysical hPhysicalLimit hn hSum
  intro final resultFrame hFinalState hSource hResult hPages hNodes hBudget hDisjoint hSaved hResultCapacity
    hResultFrame hResultScratch hN hSize hRoot
  have hSourceRoot := hSource.buffer.rootBound
  have hSource32 : source.root.toNat ≤ 4294967296 := by
    have := hSource.buffer.addressBound
    omega
  have hNonzero : source.root ≠ 0 := by
    intro h
    rw [h] at hSourceRoot
    contradiction
  have hDifferent : source.root ≠ (initialGrowthNode heap grid.size).root := by
    intro h
    have hEq := congrArg UInt64.toNat h
    simp only [regionsDisjoint, FreeNode.region] at hDisjoint
    omega
  have hParams : resultFrame.params.length = 5 := by rw [hResultFrame.params]; rfl
  apply initial_continue_spec env final (initialGrowthHeap heap grid.size) resultFrame fuel n size
    source grid (initialGrowthNode heap grid.size).root tracked hResultFrame.params hResultFrame.locals
    hResultFrame.values hResultFrame.tracker
    (Frame.internal_getElem?_of_get resultFrame 5 32 _ hParams (by rw [hResultFrame.locals]; omega) hN)
    (Frame.internal_getElem?_of_get resultFrame 5 33 _ hParams (by rw [hResultFrame.locals]; omega) hSize)
    (Frame.internal_getElem?_of_get resultFrame 5 50 _ hParams (by rw [hResultFrame.locals]; omega) hRoot)
    hNonzero hDifferent hFinalState.heapState hSource
  have hControl := hResultFrame.continued (initialGrowthNode heap grid.size).root
  have hScratchNext := hResultScratch.continued fuel n size (initialGrowthNode heap grid.size).root
    hParams hResultFrame.locals
  have hOldBelow : InitialFreeBelow (min size grid.size) (initialGrowthHeap heap grid.size).nodes := by
    rw [hNodes]
    exact hBelow
  cases tracked with
  | false =>
    exact hNext final (initialGrowthHeap heap grid.size) _ hFinalState hResult hPrefix.doubled hPages
      (initialFreeBelow_mono hOldBelow (by omega)) hBudget hSaved hResultCapacity hControl hScratchNext
  | true =>
    have hReleased := hFinalState.released source grid hSource (hSeparated rfl)
    have hResultReleased := hResult.released source hSourceRoot hSource32 hDisjoint.symm
    exact hNext _ _ _ hReleased hResultReleased hPrefix.doubled
      (by simpa only [ite_true, Heap.releaseStore, releasedStore_pages] using hPages)
      (initialFreeBelow_release source hPositive hGrow hOldBelow hCapacity)
      hBudget hSaved hResultCapacity hControl hScratchNext

#print axioms initial_growth_spec

end Project.EulerRiemann.Frozen.Execution
