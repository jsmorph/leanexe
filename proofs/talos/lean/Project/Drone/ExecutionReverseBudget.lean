import Project.Drone.ExecutionReverseRaw
import Project.Drone.ExecutionUnwindInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

theorem word_reverse_budget_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat) (hSource : s.nextLength = source.root) (hLength : s.target = UInt64.ofNat input.size)
    (hInput : BorrowedWords heap store source input) (hHeap : heap.At store)
    (hBudget : Budget store heap (reverseCost input.size + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (previous current capacity next : UInt64),
      (heap.allocate (reverseNeed input.size)).At final →
      Budget final (heap.allocate (reverseNeed input.size)) remaining pageLimit →
      (heap.allocate (reverseNeed input.size)).OwnsWords final
        (allocatedNode heap.top (reverseNeed input.size) heap.nodes) input.reverse →
      PreservesWords heap store (heap.allocate (reverseNeed input.size)) final →
      SeparateWords heap store (allocatedNode heap.top (reverseNeed input.size) heap.nodes) →
      wp Project.Drone.«module» rest Q final
        { frame params saved tail
            (reversedScratch s input.size (allocatedRoot heap.top (reverseNeed input.size) heap.nodes)
              previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top (reverseNeed input.size) heap.nodes)] } env) :
    wp Project.Drone.«module» (reverseProgram (params.length + saved.length) ++ rest) Q store
      (frame params saved tail s) env := by
  have hSize : input.size ≤ 4294967296 := by have := hInput.values.1; omega
  have hNeed := reverseNeed_toNat input.size hSize
  have hCost : 48 + (reverseNeed input.size).toNat + remaining ≤ reverseCost input.size + remaining := by
    rw [hNeed]; rfl
  have hBump := hBudget.bump (reverseNeed input.size) (by omega)
  have hFit := fun h => (hBump h).1.le
  apply word_reverse_spec env store heap params saved tail s source input hSource hLength hInput hHeap hBump
    (hBudget.pages.trans hBudget.pageLimitBound)
  intro final previous current capacity next hWrites hFinalHeap hOutput
  refine hNext final previous current capacity next hFinalHeap
    (hBudget.allocated (reverseNeed input.size) 1 remaining hCost hWrites) hOutput ?_ ?_
  · constructor
    · intro saved words hSaved
      exact hSaved.arrayWritten (reverseNeed input.size) 1 input.size hHeap (by rw [hNeed]) hFit hWrites
    · intro saved words hSaved
      exact hSaved.arrayWritten (reverseNeed input.size) 1 input.size hHeap (by rw [hNeed]) hFit hWrites
  · intro saved words hSaved
    exact allocated_region_disjoint heap.top (reverseNeed input.size) saved heap.nodes
      hSaved.rootBound hSaved.separated hSaved.below hFit

#print axioms word_reverse_budget_spec
end Project.Drone.Execution
