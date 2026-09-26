import Project.Drone.ExecutionUnwindFrame
import Project.Drone.ExecutionPreserveWords

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

theorem unwind_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel index state : Nat) (terrain history row : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (source : FreeNode) (input : Array UInt64)
    (remaining pageLimit : Nat) (hAux : aux.length = 36) (hSource : s.source = source.root)
    (hInput : BorrowedWords heap store source input) (hHeap : heap.At store)
    (hBudget : Budget store heap (pushCost input.size + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (previous current capacity next : UInt64),
      (heap.allocate (pushNeed input.size)).At final →
      Budget final (heap.allocate (pushNeed input.size)) remaining pageLimit →
      (heap.allocate (pushNeed input.size)).OwnsWords final
        (allocatedNode heap.top (pushNeed input.size) heap.nodes) (input.push s.value) →
      PreservesWords heap store (heap.allocate (pushNeed input.size)) final →
      SeparateWords heap store (allocatedNode heap.top (pushNeed input.size) heap.nodes) →
      wp Project.Drone.«module» rest Q final
        { unwindFrame fuel index state terrain history row tracked out0 out1 aux
            (pushedScratch s input.size (allocatedRoot heap.top (pushNeed input.size) heap.nodes)
              previous current capacity next) with
          values := [.i64 (allocatedRoot heap.top (pushNeed input.size) heap.nodes)] } env) :
    wp Project.Drone.«module» (WordArrayPush.program 51 ++ rest) Q store
      (unwindFrame fuel index state terrain history row tracked out0 out1 aux s) env := by
  rw [unwindFrame_as_push]
  let params := unwindParams fuel index state terrain history row
  let saved : List Value := [.i64 0, .i64 (if tracked then row else 0), .i64 0, .i64 out0, .i64 out1, .i64 0] ++ aux
  have hStart : params.length + saved.length = 51 := by simp [params, saved, unwindParams, hAux]
  rw [← hStart]
  apply word_push_budget_spec env store heap params saved [] s source input remaining pageLimit hSource hInput hHeap hBudget
  intro final previous current capacity next hFinalHeap hFinalBudget hOutput hBorrow hOwned
  simpa only [unwindFrame_as_push, params, saved] using
    hNext final previous current capacity next hFinalHeap hFinalBudget hOutput
      ⟨fun saved words h => (hBorrow saved words h).1, hOwned⟩
      (fun saved words h => (hBorrow saved words h).2)

#print axioms unwind_push_spec
end Project.Drone.Execution
