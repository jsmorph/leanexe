import Project.Drone.ExecutionAdvanceLoop
import Project.Drone.ExecutionEmptyBudget
import Project.Drone.ExecutionAdvanceFinish

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxHeartbeats 400000 in
set_option maxRecDepth 32768 in
theorem advance_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (r0 r1 : UInt64) (last : Bool) (previousNode : FreeNode) (previous : Array UInt64)
    (remaining pageLimit : Nat) (hPrevious : BorrowedWords heap initial previousNode previous)
    (hHeap : heap.At initial)
    (hBudget : Budget initial heap (56 + (advanceCost 45 0 + remaining)) pageLimit)
    (hRange : 135 ≤ previous.size) :
    TerminatesWith env Project.Drone.«module» 19 initial
      [.i64 previousNode.root, .i64 previousNode.root, .i64 (if last then 1 else 0), .i64 r1, .i64 r0]
      (AdvanceResult heap initial previousNode previous (advance r0 r1 last previous) 45 remaining pageLimit) := by
  apply advance_entry env initial r0 r1 last previousNode.root
  let params := advanceEntryParams r0 r1 last previousNode.root
  let saved := advanceEntrySaved r0 r1 last previousNode.root
  have hProgram : func19.drop 16 = emptyProgram 15 ++ func19.drop 56 := rfl
  rw [hProgram]
  apply empty_budget_spec env initial heap params saved [] zeroPushScratch
    (advanceCost 45 0 + remaining) pageLimit hHeap hBudget
  intro scratchPrevious current capacity next hEmptyHeap hEmptyBudget hEmptyOwner hBorrow hOwned
  let emptyHeap := heap.allocate 8
  let emptyNode := allocatedNode heap.top 8 heap.nodes
  have hKeep : PreservesWords heap initial emptyHeap (emptyWordsStore heap initial) :=
    ⟨fun node words h => (hBorrow node words h).1, hOwned⟩
  have hPrev := (hBorrow previousNode previous hPrevious).1
  have hSep := (hBorrow previousNode previous hPrevious).2
  have hLoop := advanceLoop_exact env (emptyWordsStore heap initial) emptyHeap r0 r1 last
    previousNode emptyNode previous #[] 45 0 remaining pageLimit hPrev hEmptyOwner hEmptyHeap hEmptyBudget
    hRange (by decide) hSep
  apply advance_finish_spec
  apply hLoop.mono
  rintro final values ⟨nextHeap, node, hFinalHeap, hFinalBudget, hFinalPrevious, hOutput,
    hSeparate, hPreserve, hFresh, rfl⟩
  refine ⟨node.root, rfl, ?_⟩
  refine ⟨nextHeap, node, hFinalHeap, hFinalBudget, hFinalPrevious, ?_, hSeparate,
    hKeep.trans hPreserve, ?_, rfl⟩
  · simpa only [advance, stateCount] using hOutput
  · intro _ saved words hSaved
    exact hFresh (by decide) saved words (hKeep.borrowed saved words hSaved)

#print axioms advance_exact
end Project.Drone.Execution
