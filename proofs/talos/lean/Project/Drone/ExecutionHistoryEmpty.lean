import Project.Drone.ExecutionHistoryFrame
import Project.Drone.ExecutionEmptyBudget
import Project.Drone.ExecutionPreserveWords

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxRecDepth 32768 in
theorem history_empty_shape : (historyLoopBody.drop 69).take 40 = emptyProgram 58 := rfl

theorem history_empty_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel index remaining pageLimit : Nat) (terrain previous history out0 out1 : UInt64)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 44) (hHeap : heap.At store)
    (hBudget : Budget store heap (56 + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ scratchPrevious current capacity next : UInt64,
      (heap.allocate 8).At (emptyWordsStore heap store) →
      Budget (emptyWordsStore heap store) (heap.allocate 8) remaining pageLimit →
      (heap.allocate 8).OwnsWords (emptyWordsStore heap store) (allocatedNode heap.top 8 heap.nodes) #[] →
      PreservesWords heap store (heap.allocate 8) (emptyWordsStore heap store) →
      SeparateWords heap store (allocatedNode heap.top 8 heap.nodes) →
      wp Project.Drone.«module» rest Q (emptyWordsStore heap store)
        { historyFrame fuel index terrain previous history out0 out1 aux
            (emptyScratch s (allocatedRoot heap.top 8 heap.nodes) scratchPrevious current capacity next) with
          values := [.i64 (allocatedRoot heap.top 8 heap.nodes)] } env) :
    wp Project.Drone.«module» ((historyLoopBody.drop 69).take 40 ++ rest) Q store
      (historyFrame fuel index terrain previous history out0 out1 aux s) env := by
  rw [history_empty_shape, historyFrame_as_push]
  let params := historyParams fuel index terrain previous history
  let saved : List Value := [.i64 0, .i64 0, .i64 0, .i64 out0, .i64 out1, .i64 0] ++ aux
  have hStart : params.length + saved.length = 58 := by simp [params, saved, historyParams, hAux]
  rw [← hStart]
  apply empty_budget_spec env store heap params saved [] s remaining pageLimit hHeap hBudget
  intro scratchPrevious current capacity next hFinalHeap hFinalBudget hOutput hBorrow hOwned
  simpa only [historyFrame_as_push, params, saved] using
    hNext scratchPrevious current capacity next hFinalHeap hFinalBudget hOutput
      ⟨fun saved words h => (hBorrow saved words h).1, hOwned⟩
      (fun saved words h => (hBorrow saved words h).2)

#print axioms history_empty_spec
end Project.Drone.Execution
