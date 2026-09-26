import Project.Drone.ExecutionHistoryEmpty
import Project.Drone.ExecutionHistoryAdvanceCall
import Project.Drone.ExecutionAdvanceLoop

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
theorem history_layer_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel index remaining pageLimit : Nat) (terrain history out0 out1 r0 r1 : UInt64) (last : Bool)
    (previousNode : FreeNode) (previous : Array UInt64) (aux : List Value) (s : Scratch)
    (hAux : aux.length = 44) (hCount : aux[1]? = some (.i64 45)) (hZero : aux[2]? = some (.i64 0))
    (hR0 : aux[7]? = some (.i64 r0)) (hR1 : aux[12]? = some (.i64 r1))
    (hLast : aux[13]? = some (.i64 (if last then 1 else 0)))
    (hOwner : aux[14]? = some (.i64 previousNode.root)) (hPointer : aux[15]? = some (.i64 previousNode.root))
    (hPrevious : BorrowedWords heap store previousNode previous) (hRange : 135 ≤ previous.size)
    (hHeap : heap.At store) (hBudget : Budget store heap (56 + (advanceCost 45 0 + remaining)) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (node : FreeNode) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 44 → nextAux[21]? = some (.i64 node.root) → nextAux[22]? = some (.i64 node.root) →
      nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final node (advance r0 r1 last previous) →
      PreservesWords heap store nextHeap final → SeparateWords heap store node →
      wp Project.Drone.«module» rest Q final
        (historyFrame fuel index terrain previousNode.root history out0 out1 nextAux nextScratch) env) :
    wp Project.Drone.«module» ((historyLoopBody.drop 69).take 61 ++ rest) Q store
      (historyFrame fuel index terrain previousNode.root history out0 out1 aux s) env := by
  have hCode : (historyLoopBody.drop 69).take 61 = (historyLoopBody.drop 69).take 40 ++
      (historyLoopBody.drop 109).take 21 := rfl
  rw [hCode, List.append_assoc]
  apply history_empty_spec env store heap fuel index (advanceCost 45 0 + remaining) pageLimit
    terrain previousNode.root history out0 out1 aux s hAux hHeap hBudget
  intro scratchPrevious current capacity next hEmptyHeap hEmptyBudget hEmptyOwner hKeep hSeedFresh
  let emptyHeap := heap.allocate 8
  let seed := allocatedNode heap.top 8 heap.nodes
  have hLoop := advanceLoop_exact env (emptyWordsStore heap store) emptyHeap r0 r1 last
    previousNode seed previous #[] 45 0 remaining pageLimit (hKeep.borrowed _ _ hPrevious)
    hEmptyOwner hEmptyHeap hEmptyBudget hRange (by decide) (hSeedFresh _ _ hPrevious)
  let P : Store Unit → UInt64 → Prop := fun final root =>
    ∃ nextHeap node, node.root = root ∧ nextHeap.At final ∧ Budget final nextHeap remaining pageLimit ∧
      nextHeap.OwnsWords final node (advance r0 r1 last previous) ∧
      PreservesWords heap store nextHeap final ∧ SeparateWords heap store node
  have hCall : TerminatesWith env Project.Drone.«module» 18 (emptyWordsStore heap store)
      [.i64 seed.root, .i64 seed.root, .i64 previousNode.root, .i64 previousNode.root,
        .i64 (if last then 1 else 0), .i64 r1, .i64 r0, .i64 0, .i64 45]
      (fun final values => ∃ root : UInt64, values = [.i64 root, .i64 root] ∧ P final root) := by
    apply hLoop.mono
    rintro final values ⟨nextHeap, node, hFinalHeap, hFinalBudget, _, hOutput, _, hPreserve, hFresh, rfl⟩
    refine ⟨node.root, rfl, nextHeap, node, rfl, hFinalHeap, hFinalBudget, ?_, hKeep.trans hPreserve, ?_⟩
    · simpa only [advance, stateCount] using hOutput
    · intro saved words hSaved
      exact hFresh (by decide) saved words (hKeep.borrowed saved words hSaved)
  apply history_advance_call_spec env _ fuel index terrain previousNode.root history out0 out1 seed.root
    r0 r1 last aux _ hAux hCount hZero hR0 hR1 hLast hOwner hPointer P hCall
  rintro final root nextAux hLength hOut0 hOut1 ⟨nextHeap, node, rfl, hFinalHeap, hFinalBudget, hOutput, hPreserve, hFresh⟩
  exact hNext final nextHeap node nextAux _ hLength hOut0 hOut1 hFinalHeap hFinalBudget hOutput hPreserve hFresh

#print axioms history_layer_spec
end Project.Drone.Execution
