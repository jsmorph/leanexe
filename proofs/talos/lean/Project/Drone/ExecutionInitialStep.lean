import Project.Drone.ExecutionInitialPrepare
import Project.Drone.ExecutionInitialPushThree
import Project.Drone.ExecutionInitialTail
import Project.Drone.ExecutionHeap

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxHeartbeats 300000 in
set_option maxRecDepth 32768 in
theorem initial_step_spec (env : HostEnv Unit) (store initial : Store Unit) (heap initialHeap : Heap)
    (seed : UInt64) (node : FreeNode) (row : Array UInt64) (state remaining pageLimit : Nat)
    (tracked : Bool) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (hAux : aux.length = 21) (hState : state + 1 < UInt64.size)
    (hRow : heap.OwnsWords store node row) (hHeap : heap.At store)
    (hBudget : Budget store heap (rowPushCost row.size + remaining) pageLimit)
    (hPreserve : PreservesWords initialHeap initial heap store)
    (hTracked : tracked = true → SeparateWords initialHeap initial node)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (nextNode : FreeNode)
      (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 21 → nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final nextNode (((row.push (initialWord state)).push (initialWord state)).push 0) →
      PreservesWords initialHeap initial nextHeap final → SeparateWords initialHeap initial nextNode →
      Q (.Break 0 final (initialFrame seed nextNode.root (state + 1) true nextAux nextScratch
        nextNode.root nextNode.root))) :
    wp Project.Drone.«module» (initialLoopBody.drop 4) Q store
      (initialFrame seed node.root state tracked aux s out0 out1) env := by
  have hBody : initialLoopBody.drop 4 = (initialLoopBody.drop 4).take 21 ++
      (initialLoopBody.drop 25).take 211 ++ initialLoopBody.drop 236 := rfl
  rw [hBody]
  apply initial_prepare_spec env store seed node.root state tracked aux s out0 out1 hAux (by omega)
  intro prepared hLength hValue
  apply initial_three_push_spec env store heap seed node.root state tracked prepared
    { s with source := node.root, value := initialWord state } out0 out1 node row remaining pageLimit
    hLength hValue rfl (borrow_owned hRow) hHeap hBudget
  intro pushed nextHeap nextNode pushedAux nextScratch hPushedLength hPushedHeap hPushedBudget hOutput hKeep hFresh
  have hOld := hKeep.owned node row hRow
  have hSeparate := hFresh node row (borrow_owned hRow)
  have hKept := hPreserve.trans hKeep
  have hFreshOriginal : SeparateWords initialHeap initial nextNode := by
    intro saved words hSaved
    exact hFresh saved words (hPreserve.borrowed saved words hSaved)
  have hOldNonzero : node.root ≠ 0 := by
    intro h; have := hRow.buffer.rootBound; rw [h] at this; contradiction
  have hNewNonzero : nextNode.root ≠ 0 := by
    intro h; have := hOutput.buffer.rootBound; rw [h] at this; contradiction
  cases tracked with
  | false =>
    apply initial_tail_spec env pushed pushed seed node.root nextNode.root state false pushedAux nextScratch
      out0 out1 hPushedLength hState hOldNonzero hNewNonzero (fun _ => rfl) (by simp)
    intro nextAux finalScratch hLength
    exact hNext pushed nextHeap nextNode nextAux finalScratch hLength hPushedHeap hPushedBudget
      hOutput hKept hFreshOriginal
  | true =>
    have hRelease := release_words_exact env pushed nextHeap node row hPushedHeap hOld
    let released := nextHeap.releaseStore pushed node
    have hCall : TerminatesWith env Project.Drone.«module» 29 pushed [.i64 node.root]
        (fun finish values => finish = released ∧ values = []) := by
      apply hRelease.mono
      rintro finish values ⟨hValues, hFinish, _⟩
      exact ⟨hFinish, hValues⟩
    apply initial_tail_spec env pushed released seed node.root nextNode.root state true pushedAux nextScratch
      out0 out1 hPushedLength hState hOldNonzero hNewNonzero (by simp) (fun _ => hCall)
    intro nextAux finalScratch hLength
    have hRoot32 : node.root.toNat ≤ 4294967296 := by have := hOld.buffer.addressBound; omega
    apply hNext released (nextHeap.release node) nextNode nextAux finalScratch hLength
    · exact nextHeap.release_at pushed node hPushedHeap hOld.buffer.rootBound hOld.buffer.addressBound
        hOld.buffer.memoryBound hOld.buffer.fresh.2.2.1 hOld.below hOld.separated
    · exact hPushedBudget.released node
    · exact hOutput.released node hOld.buffer.rootBound hRoot32 (word_regions_symm hSeparate)
    · exact hKept.released node hOld.buffer.rootBound hRoot32 (hTracked rfl)
    · exact hFreshOriginal

#print axioms initial_step_spec
end Project.Drone.Execution
