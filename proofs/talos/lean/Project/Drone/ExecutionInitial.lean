import Project.Drone.ExecutionInitialLoop
import Project.Drone.ExecutionInitialEntry
import Project.Drone.ExecutionInitialFinish
import Project.Drone.ExecutionArrayResult

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxHeartbeats 300000 in
set_option maxRecDepth 32768 in
theorem initial_exact (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (remaining pageLimit : Nat) (hHeap : heap.At store)
    (hBudget : Budget store heap (56 + (advanceCost 45 0 + remaining)) pageLimit) :
    TerminatesWith env Project.Drone.«module» 23 store []
      (FreshArrayResult heap store LeanExe.Examples.Drone.initial remaining pageLimit) := by
  apply initial_entry
  apply empty_budget_spec env store heap [] (List.replicate 22 (.i64 0)) (List.replicate 12 (.i64 0))
    zeroPushScratch (advanceCost 45 0 + remaining) pageLimit hHeap hBudget
  intro previous current capacity next hEmptyHeap hEmptyBudget hEmptyOwner hBorrow hOwned
  let emptyHeap := heap.allocate 8
  let seed := allocatedNode heap.top 8 heap.nodes
  have hKeep : PreservesWords heap store emptyHeap (emptyWordsStore heap store) :=
    ⟨fun node words h => (hBorrow node words h).1, hOwned⟩
  have hSeedFresh : SeparateWords heap store seed := fun node words h => (hBorrow node words h).2
  have hCode : func23.drop 40 = (func23.drop 40).take 17 ++
      (.block 0 0 [.loop 0 0 initialLoopBody] :: func23.drop 58) := rfl
  rw [hCode]
  apply initial_start_spec
  intro aux scratch hAux
  apply initial_loop_spec env (emptyWordsStore heap store) emptyHeap seed remaining pageLimit
    aux scratch 0 0 hAux hEmptyHeap hEmptyOwner hEmptyBudget
  intro final nextHeap node nextAux nextScratch out0 out1 hLength hFinalHeap hFinalBudget hOutput hPreserve hFresh
  have hSeedOwner := hPreserve.owned seed #[] hEmptyOwner
  have hSeparate := hFresh seed #[] (borrow_owned hEmptyOwner)
  have hSeedNonzero : seed.root ≠ 0 := by
    intro h; have := hSeedOwner.buffer.rootBound; rw [h] at this; contradiction
  have hDifferent : seed.root ≠ node.root :=
    word_regions_ne hSeedOwner.buffer.rootBound hOutput.buffer.rootBound hSeparate
  let released := nextHeap.releaseStore final seed
  have hRelease := release_words_exact env final nextHeap seed #[] hFinalHeap hSeedOwner
  have hCall : TerminatesWith env Project.Drone.«module» 29 final [.i64 seed.root]
      (fun finish values => finish = released ∧ values = []) := by
    apply hRelease.mono
    rintro finish values ⟨hValues, hFinish, _⟩
    exact ⟨hFinish, hValues⟩
  apply initial_finish_spec env final released seed.root node.root nextAux nextScratch out0 out1
    hLength hSeedNonzero hDifferent hCall
  have hRoot32 : seed.root.toNat ≤ 4294967296 := by have := hSeedOwner.buffer.addressBound; omega
  refine ⟨nextHeap.release seed, node, ?_, hFinalBudget.released seed, ?_, ?_, ?_, rfl⟩
  · exact nextHeap.release_at final seed hFinalHeap hSeedOwner.buffer.rootBound hSeedOwner.buffer.addressBound
      hSeedOwner.buffer.memoryBound hSeedOwner.buffer.fresh.2.2.1 hSeedOwner.below hSeedOwner.separated
  · exact hOutput.released seed hSeedOwner.buffer.rootBound hRoot32 (word_regions_symm hSeparate)
  · exact (hKeep.trans hPreserve).released seed hSeedOwner.buffer.rootBound hRoot32 hSeedFresh
  · intro saved words hSaved
    exact hFresh saved words (hKeep.borrowed saved words hSaved)

#print axioms initial_exact
end Project.Drone.Execution
