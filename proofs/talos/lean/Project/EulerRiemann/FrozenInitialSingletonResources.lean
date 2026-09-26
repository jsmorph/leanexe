import Project.EulerRiemann.FrozenInitialSingletonBuild

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

theorem initial_singleton_state (initial : Store Unit) (heap : Heap) (cell : Traversal.Cell)
    (hHeap : heap.At initial) (hBelow : InitialFreeBelow 1 heap.nodes)
    (hFit : heap.top.toNat + 48 + 64 < 4294967296) (hPages : initial.mem.pages ≤ 65536)
    (hFinalHeap : (heap.allocate 64).At (initialSingletonFinalStore initial heap cell))
    (hWrites : Memory.WritesGrid (heap.allocateStore initial 64)
      (initialSingletonFinalStore initial heap cell) (heap.top + 48) 1) :
    RetryStoreAt initial heap (initialSingletonFinalStore initial heap cell) (heap.allocate 64) ∧
      ∀ (saved : FreeNode) (grid : Array Traversal.Cell), heap.Owns initial saved grid →
        regionsDisjoint saved.region (allocatedNode heap.top 64 heap.nodes).region := by
  have hNeed : normalizedCapacity (UInt64.ofNat 1) 7 = 64 := rfl
  have hInitial : RetryStoreAt initial heap initial heap := ⟨hHeap, hPages, rfl, fun _ _ h => h⟩
  have h := hInitial.initialAllocated (final := initialSingletonFinalStore initial heap cell)
    1 (by decide) hBelow (by simpa only [initialBytes] using hFit)
    (by simpa only [hNeed] using hFinalHeap) (by simpa only [hNeed] using hWrites)
  simpa only [hNeed] using h

theorem initial_singleton_reserve (heap : Heap) (target limit : Nat)
    (hBelow : InitialFreeBelow 1 heap.nodes) (hFit : heap.top.toNat + 48 + 64 ≤ 4294967296)
    (hReserve : heap.top.toNat + 112 + initialRemainingBytes 1 20 target ≤ limit) :
    (heap.allocate 64).top.toNat + initialRemainingBytes 1 20 target ≤ limit := by
  have hNeed : normalizedCapacity (UInt64.ofNat 1) 7 = 64 := rfl
  have hTop := initial_allocated_top heap 1 (by decide) hBelow (by simpa only [initialBytes] using hFit)
  have hTop' : (heap.allocate 64).top.toNat = heap.top.toNat + 112 := by
    simpa only [hNeed, initialBytes, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc] using hTop
  rw [hTop']
  exact hReserve

theorem initial_singleton_pages (initial : Store Unit) (heap : Heap) (cell : Traversal.Cell)
    (pageLimit : Nat) (hPages : initial.mem.pages ≤ pageLimit)
    (hFit : heap.top.toNat + 112 ≤ pageLimit * 65536)
    (hWrites : Memory.WritesGrid (heap.allocateStore initial 64)
      (initialSingletonFinalStore initial heap cell) (heap.top + 48) 1) :
    (initialSingletonFinalStore initial heap cell).mem.pages ≤ pageLimit := by
  have hNeed : normalizedCapacity (UInt64.ofNat 1) 7 = 64 := rfl
  exact initial_allocated_pages heap initial (initialSingletonFinalStore initial heap cell) 1 pageLimit
    (by decide) hPages (by simp only [initialBytes]; omega) (by simpa only [hNeed] using hWrites)

#print axioms initial_singleton_state
#print axioms initial_singleton_reserve
#print axioms initial_singleton_pages

end Project.EulerRiemann.Frozen.Execution
