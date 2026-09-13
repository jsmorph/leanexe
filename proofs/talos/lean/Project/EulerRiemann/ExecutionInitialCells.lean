import Project.EulerRiemann.InitialCellsGuard
import Project.EulerRiemann.InitialSingletonResources
import Project.EulerRiemann.AdvanceResources

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

theorem initial_cells_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (n limit pageLimit : Nat) (hn2 : 2 ≤ n) (hn : n ≤ 800)
    (hHeap : heap.At initial) (hBelow : InitialFreeBelow 1 heap.nodes)
    (hReserve : heap.top.toNat + 112 + initialRemainingBytes 1 20 (n * n) ≤ limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hPhysicalLimit : limit ≤ pageLimit * 65536) :
    TerminatesWith env module 96 initial [.i64 (UInt64.ofNat n)]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root] ∧
        RetryStoreAt initial heap final finalHeap ∧
        finalHeap.Owns final result (Traversal.initialCells n) ∧
        result.capacity.toNat = initialBytes (n * n) ∧ finalHeap.top.toNat ≤ limit ∧
        final.mem.pages ≤ pageLimit ∧
        (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region)) := by
  have hSize : n * n ≤ 640000 := Nat.mul_le_mul hn hn
  have hSizePositive : 1 ≤ n * n := by nlinarith
  have hNeed : normalizedCapacity (UInt64.ofNat 1) 7 = 64 := rfl
  have hNone : takeFirstFitFrom 0 64 heap.nodes = none := by
    simpa only [hNeed] using initial_no_fit 1 (by decide) heap.nodes hBelow
  have hFit : heap.top.toNat + 48 + 64 < 4294967296 := by omega
  have hAllocationCap : FixedArrayBump.requiredPages heap.top 64 ≤ initial.memoryCap module 0 := by
    have h := initial_allocation_cap initial heap 1 (by decide) (by simp only [initialBytes]; omega)
    simpa only [hNeed] using h
  refine TerminatesWith.of_wp_entry_for (f := func96Def) rfl ?_ (by decide)
  change wp module func96 _ initial (initialCellsEntryFrame n) env
  apply initial_cells_guard_spec env initial n hn2 hn
  rw [initial_cells_body_shape]
  apply initial_singleton_build_spec env initial heap n hn hHeap hNone hFit (hPages.trans hPageLimit) hAllocationCap
  intro previousAfter hSingletonHeap hSingletonOwner hWrites
  let singleton := initialSingletonFinalStore initial heap (Traversal.initialCell n 0)
  let singletonHeap := heap.allocate 64
  let source := allocatedNode heap.top 64 heap.nodes
  have hRoot : source.root = heap.top + 48 := by simp [source, allocatedNode, allocatedRoot, hNone]
  have hSingletonState := initial_singleton_state initial heap (Traversal.initialCell n 0)
    hHeap hBelow hFit (hPages.trans hPageLimit) hSingletonHeap hWrites
  have hSingletonCapacity : source.capacity.toNat = initialBytes 1 := by
    simp [source, allocatedNode, allocatedCapacity, hNone, initialBytes]
  have hSingletonBelow : InitialFreeBelow (min (n * n) 1) singletonHeap.nodes := by
    simpa only [singletonHeap, initial_allocateHeap_eq heap 64 hNone, Nat.min_eq_right hSizePositive] using hBelow
  have hSingletonReserve := initial_singleton_reserve heap (n * n) limit hBelow hFit.le hReserve
  have hSingletonPages := initial_singleton_pages initial heap (Traversal.initialCell n 0) pageLimit
    hPages (by omega) hWrites
  have hGrow := initial_grow_exact env singleton singletonHeap source #[Traversal.initialCell n 0]
    n (n * n) limit pageLimit hn hSize rfl hSingletonHeap hSingletonOwner hSingletonCapacity hSingletonBelow
    hSingletonReserve hLimit (by rw [hSingletonState.1.cap]; exact hCap)
    hSingletonPages hPageLimit hPhysicalLimit
  rw [hRoot] at hGrow
  wp_run [initialSingletonBuiltFrame, initialSingletonDataFrame, initialSingletonStageFrame,
    initialSingletonAllocatedFrame, initialSingletonSaved, FixedArraySearch.frame,
    FixedArrayFold.resultFrame, Memory.cellWords, List.set, List.length_set, List.getElem?_set,
    List.cons_append, List.nil_append, List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]
  refine wp_call_tw hGrow ?_
  rintro current values ⟨currentHeap, result, hValues, hCurrent, hOwner, hCapacity, hTop, hCurrentPages, hSeparated⟩
  subst values
  have hSource := hCurrent.held source #[Traversal.initialCell n 0] hSingletonOwner
  have hOldNew := hSeparated source #[Traversal.initialCell n 0] hSingletonOwner
  have hState := hSingletonState.1.trans hCurrent
  have hFinalState := hState.released source #[Traversal.initialCell n 0] hSource hSingletonState.2
  have hRoot32 : source.root.toNat ≤ 4294967296 := by have := hSource.buffer.addressBound; omega
  have hFinalOwner := hOwner.released source hSource.buffer.rootBound hRoot32 (regionsDisjoint_symm hOldNew)
  have hRelease := release_owned env current currentHeap source #[Traversal.initialCell n 0]
    hCurrent.heapState hSource
  rw [hRoot] at hRelease
  wp_run [List.set, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]
  refine wp_call_tw hRelease ?_
  rintro final values ⟨hValues, hFinal, _⟩
  subst values
  subst final
  wp_run [FixedArrayEqNode.branchPost, List.set, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte]
  refine ⟨currentHeap.release source, result, rfl, hFinalState, ?_, hCapacity, hTop, ?_, ?_⟩
  · simpa [Traversal.initialCells, hn2, hn] using hFinalOwner
  · simpa only [Heap.releaseStore, releasedStore_pages] using hCurrentPages
  · intro saved savedGrid hSaved
    exact hSeparated saved savedGrid (hSingletonState.1.held saved savedGrid hSaved)

#print axioms initial_cells_exact

end Project.EulerRiemann.Execution
