import Project.Drone.ExecutionEmptyProgram
import Project.Drone.ExecutionPushBudget

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

theorem empty_budget_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (s : Scratch) (remaining pageLimit : Nat)
    (hHeap : heap.At store) (hBudget : Budget store heap (56 + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      (heap.allocate 8).At (emptyWordsStore heap store) →
      Budget (emptyWordsStore heap store) (heap.allocate 8) remaining pageLimit →
      (heap.allocate 8).OwnsWords (emptyWordsStore heap store)
        (allocatedNode heap.top 8 heap.nodes) #[] →
      (∀ saved words, BorrowedWords heap store saved words →
        BorrowedWords (heap.allocate 8) (emptyWordsStore heap store) saved words ∧
        regionsDisjoint saved.region (allocatedNode heap.top 8 heap.nodes).region) →
      (∀ saved words, heap.OwnsWords store saved words →
        (heap.allocate 8).OwnsWords (emptyWordsStore heap store) saved words) →
      wp Project.Drone.«module» rest Q (emptyWordsStore heap store)
        { WordArrayPush.frame params saved tail
            (emptyScratch s (allocatedRoot heap.top 8 heap.nodes) previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top 8 heap.nodes)] } env) :
    wp Project.Drone.«module» (emptyProgram (params.length + saved.length) ++ rest)
      Q store (WordArrayPush.frame params saved tail s) env := by
  have hBump := hBudget.bump 8 (by change 48 + 8 ≤ 56 + remaining; omega)
  have hFit := fun h => (hBump h).1.le
  have hOwned := emptyWords_owned heap store hHeap (fun h => (hBump h).1)
  have hWrites := (emptyWords_memory heap store hHeap (fun h => (hBump h).1)).1
  apply empty_program_spec env store heap params saved tail s hHeap hBump
    (hBudget.pages.trans hBudget.pageLimitBound) Q rest
  intro previous current capacity next
  apply hNext previous current capacity next hOwned.1
    (hBudget.allocated 8 1 remaining (by change 48 + 8 + remaining ≤ 56 + remaining; omega) hWrites)
    hOwned.2.1
  · intro saved words hSaved
    refine ⟨hSaved.arrayWritten 8 1 0 hHeap (by decide) hFit hWrites, ?_⟩
    exact allocated_region_disjoint heap.top 8 saved heap.nodes
      hSaved.rootBound hSaved.separated hSaved.below hFit
  · intro saved words hSaved
    exact (hOwned.2.2 saved words hSaved).1

#print axioms empty_budget_spec
end Project.Drone.Execution
