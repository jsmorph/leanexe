import Project.Drone.ExecutionComputeFrame
import Project.Drone.ExecutionEmptyBudget
import Project.Drone.ExecutionArrayResult

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxRecDepth 32768 in
theorem compute_reject_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (badHeight : Bool) (terrain : UInt64) (aux : List Value) (s : Scratch)
    (remaining pageLimit : Nat) (hAux : aux.length = 30) (hHeap : heap.At store)
    (hBudget : Budget store heap (56 + remaining) pageLimit) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 30 → nextScratch.target = root →
      FreshArrayResult heap store #[] remaining pageLimit final [.i64 root, .i64 root] →
      wp Project.Drone.«module» rest Q final (computeFrame terrain nextAux nextScratch) env) :
    wp Project.Drone.«module» ((if badHeight then computeBadHeight else computeReject) ++ rest) Q store
      (computeFrame terrain aux s) env := by
  have hCode : (if badHeight then computeBadHeight else computeReject) = emptyProgram 31 ++
      (if badHeight then computeBadHeight.drop 40 else computeReject.drop 40) := by cases badHeight <;> rfl
  rw [hCode, List.append_assoc]
  have hBase : ([Value.i64 terrain].length + aux.length) = 31 := by simp [hAux]
  rw [← hBase]
  apply empty_budget_spec env store heap [.i64 terrain] aux [] s remaining pageLimit hHeap hBudget
  intro previous current capacity next hFinalHeap hFinalBudget hOutput hBorrow hOwned
  let root := allocatedRoot heap.top 8 heap.nodes
  let staged := emptyScratch s root previous current capacity next
  have hResult : FreshArrayResult heap store #[] remaining pageLimit (emptyWordsStore heap store) [.i64 root, .i64 root] := by
    refine ⟨heap.allocate 8, allocatedNode heap.top 8 heap.nodes, hFinalHeap, hFinalBudget, hOutput, ?_, ?_, rfl⟩
    · exact ⟨fun node words h => (hBorrow node words h).1, hOwned⟩
    · exact fun node words h => (hBorrow node words h).2
  cases badHeight with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, computeReject, func25, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.drop, List.cons_append, List.nil_append]
    wp_compute_frame [hAux]
    exact hNext _ root (aux.set 0 (.i64 root)) { staged with nextLength := root, target := root }
      (by simp [hAux]) rfl hResult
  | true =>
    simp only [↓reduceIte, computeBadHeight, computeValidate, func25, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.drop, List.cons_append, List.nil_append]
    wp_compute_frame [hAux]
    exact hNext _ root aux { staged with count := root, nextLength := root, target := root } hAux rfl hResult

#print axioms compute_reject_spec
end Project.Drone.Execution
