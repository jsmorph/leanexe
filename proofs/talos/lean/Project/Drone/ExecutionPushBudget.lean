import Project.Drone.ExecutionPush
import Project.EulerRiemann.OutputBudget

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

abbrev Budget (store : Store Unit) (heap : Heap) (remaining pageLimit : Nat) : Prop :=
  OutputBudget store heap remaining pageLimit Project.Drone.«module»

def pushCost (size : Nat) : Nat := 48 + 8 * (size + 2)

theorem word_push_budget_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat)
    (hSource : s.source = source.root) (hInput : BorrowedWords heap store source input)
    (hHeap : heap.At store) (hBudget : Budget store heap (pushCost input.size + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (previous current capacity next : UInt64),
      (heap.allocate (pushNeed input.size)).At final →
      Budget final (heap.allocate (pushNeed input.size)) remaining pageLimit →
      (heap.allocate (pushNeed input.size)).OwnsWords final
        (allocatedNode heap.top (pushNeed input.size) heap.nodes) (input.push s.value) →
      (∀ saved words, BorrowedWords heap store saved words →
        BorrowedWords (heap.allocate (pushNeed input.size)) final saved words ∧
        regionsDisjoint saved.region (allocatedNode heap.top (pushNeed input.size) heap.nodes).region) →
      (∀ saved words, heap.OwnsWords store saved words →
        (heap.allocate (pushNeed input.size)).OwnsWords final saved words) →
      wp Project.Drone.«module» rest Q final
        { WordArrayPush.frame params saved tail
            (pushedScratch s input.size (allocatedRoot heap.top (pushNeed input.size) heap.nodes)
              previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top (pushNeed input.size) heap.nodes)] } env) :
    wp Project.Drone.«module» (WordArrayPush.program (params.length + saved.length) ++ rest)
      Q store (WordArrayPush.frame params saved tail s) env := by
  have hSize : input.size + 1 ≤ 4294967296 := by have := hInput.values.1; omega
  have hNeed := pushNeed_toNat input.size hSize
  have hCost : 48 + (pushNeed input.size).toNat + remaining ≤ pushCost input.size + remaining := by
    rw [hNeed]; rfl
  have hBump := hBudget.bump (pushNeed input.size) (by omega)
  have hFit := fun h => (hBump h).1.le
  apply word_push_spec env store heap params saved tail s source input hSource hInput hHeap
    hBump (hBudget.pages.trans hBudget.pageLimitBound) Q rest
  intro final previous current capacity next hWrites hFinalHeap _ hOutput
  apply hNext final previous current capacity next hFinalHeap
    (hBudget.allocated (pushNeed input.size) 1 remaining hCost hWrites) hOutput
  · intro saved words hSaved
    refine ⟨hSaved.arrayWritten (pushNeed input.size) 1 (input.size + 1) hHeap
      (by rw [hNeed]) hFit (by simpa only [Nat.add_assoc] using hWrites), ?_⟩
    exact allocated_region_disjoint heap.top (pushNeed input.size) saved heap.nodes
      hSaved.rootBound hSaved.separated hSaved.below hFit
  · intro saved words hSaved
    exact hSaved.arrayWritten (pushNeed input.size) 1 (input.size + 1) hHeap
      (by rw [hNeed]) hFit (by simpa only [Nat.add_assoc] using hWrites)

#print axioms word_push_budget_spec
end Project.Drone.Execution
