import Project.Drone.ExecutionUnwindPushTwo
import Project.Drone.ExecutionUnwindParent
import Project.Drone.ExecutionUnwindTailPrepare
import Project.Drone.ExecutionUnwindCleanup
import Project.Drone.ExecutionWordBounds
import Project.Drone.ExecutionHeap

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem unwind_step_spec (env : HostEnv Unit) (store initial : Store Unit) (heap initialHeap : Heap)
    (fuel index state remaining pageLimit : Nat) (terrainNode historyNode rowNode : FreeNode)
    (terrain history row : Array UInt64) (tracked : Bool) (out0 out1 : UInt64) (aux : List Value) (s : Scratch)
    (hAux : aux.length = 36) (hState : state < UInt64.size) (hIndex : index < terrain.size)
    (hRead : 0 < index → (index - 1) * 45 + state < history.size)
    (hTerrain : BorrowedWords heap store terrainNode terrain) (hHistory : BorrowedWords heap store historyNode history)
    (hRow : heap.OwnsWords store rowNode row) (hHeap : heap.At store)
    (hBudget : Budget store heap (pushCost row.size + (pushCost (row.size + 1) + remaining)) pageLimit)
    (hTerrainSep : regionsDisjoint terrainNode.region rowNode.region)
    (hHistorySep : regionsDisjoint historyNode.region rowNode.region)
    (hPreserve : PreservesWords initialHeap initial heap store)
    (hTracked : tracked = true → SeparateWords initialHeap initial rowNode)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (node : FreeNode) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 36 → nextAux[33]? = some (.i64 0) → nextAux[35]? = aux[35]? → nextHeap.At final → Budget final nextHeap remaining pageLimit →
      BorrowedWords nextHeap final terrainNode terrain → BorrowedWords nextHeap final historyNode history →
      nextHeap.OwnsWords final node ((row.push (speed state)).push (altitude (floorAt terrain index) state)) →
      regionsDisjoint terrainNode.region node.region → regionsDisjoint historyNode.region node.region →
      PreservesWords initialHeap initial nextHeap final → SeparateWords initialHeap initial node →
      Q (.Break 0 final (unwindFrame fuel (index - 1) (unwindParent index state history)
        terrainNode.root historyNode.root node.root true out0 out1 nextAux nextScratch))) :
    wp Project.Drone.«module» (unwindLoopBody.drop 7) Q store
      (unwindFrame (fuel + 1) index state terrainNode.root historyNode.root rowNode.root tracked out0 out1 aux s) env := by
  have hCode : unwindLoopBody.drop 7 = (unwindLoopBody.drop 7).take 169 ++
      (unwindLoopBody.drop 176).take 8 ++ (unwindLoopBody.drop 184).take 23 ++ unwindLoopBody.drop 207 := rfl
  rw [hCode]
  apply unwind_two_push_spec env store heap (fuel + 1) index state remaining pageLimit terrainNode rowNode terrain row
    historyNode.root out0 out1 tracked aux s hAux hState hTerrain hIndex hRow hHeap hBudget
  intro pushed nextHeap node pushedAux pushedScratch hLength hPushed35 hPushedHeap hPushedBudget hOutput hKeep hFresh
  have hCurrentTerrain := hKeep.borrowed _ _ hTerrain
  have hCurrentHistory := hKeep.borrowed _ _ hHistory
  have hOld := hKeep.owned _ _ hRow
  have hOldNew := hFresh _ _ (borrow_owned hRow)
  have hNewTerrain := hFresh _ _ hTerrain
  have hNewHistory := hFresh _ _ hHistory
  have hKept := hPreserve.trans hKeep
  have hFreshOriginal : SeparateWords initialHeap initial node := by
    intro saved words hSaved
    exact hFresh saved words (hPreserve.borrowed saved words hSaved)
  have hIndex64 : index < UInt64.size := lt_trans hIndex hTerrain.values.size_lt
  apply unwind_parent_spec env pushed (fuel + 1) index state terrainNode.root historyNode.root rowNode.root node.root
    tracked out0 out1 pushedAux pushedScratch history hLength hIndex64 hState hCurrentHistory.values hRead
  intro parentAux parentScratch hParentLength hParent35 hRoot0 hRoot1 hParent
  apply unwind_tail_prepare_spec env pushed (fuel + 1) index state (unwindParent index state history)
    terrainNode.root historyNode.root rowNode.root node.root tracked out0 out1 parentAux parentScratch
    hParentLength hIndex64 hRoot0 hRoot1 hParent
  let prepared := unwindTailAux parentAux index (unwindParent index state history) terrainNode.root historyNode.root node.root
  let staged := { parentScratch with source := UInt64.ofNat index, length := 1 }
  have hPrepared : prepared.length = 36 := by simp [prepared, unwindTailAux, hParentLength]
  have hPrepared35 : prepared[35]? = aux[35]? := by
    simpa [prepared, unwindTailAux] using hParent35.trans hPushed35
  have hOldTerrain : rowNode.root ≠ terrainNode.root :=
    Ne.symm (word_regions_ne hTerrain.rootBound hRow.buffer.rootBound hTerrainSep)
  have hOldHistory : rowNode.root ≠ historyNode.root :=
    Ne.symm (word_regions_ne hHistory.rootBound hRow.buffer.rootBound hHistorySep)
  have hOldRoot : rowNode.root ≠ node.root := word_regions_ne hRow.buffer.rootBound hOutput.buffer.rootBound hOldNew
  cases tracked with
  | false =>
    apply unwind_cleanup_spec env pushed pushed fuel index state (index - 1) (unwindParent index state history)
      terrainNode.root historyNode.root rowNode.root node.root false out0 out1 prepared staged hPrepared
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (borrowed_root_ne_zero hTerrain) (borrowed_root_ne_zero hHistory) (owned_root_ne_zero hRow)
      hOldTerrain hOldHistory hOldRoot (fun _ => rfl) (by simp)
    intro nextAux hAuxLength hFinal33 hFinal35
    exact hNext pushed nextHeap node nextAux staged hAuxLength hFinal33 (hFinal35.trans hPrepared35) hPushedHeap hPushedBudget hCurrentTerrain
      hCurrentHistory hOutput hNewTerrain hNewHistory hKept hFreshOriginal
  | true =>
    let released := nextHeap.releaseStore pushed rowNode
    have hRelease := release_words_exact env pushed nextHeap rowNode row hPushedHeap hOld
    have hCall : TerminatesWith env Project.Drone.«module» 29 pushed [.i64 rowNode.root]
        (fun finish values => finish = released ∧ values = []) := by
      apply hRelease.mono
      rintro finish values ⟨hValues, hFinish, _⟩
      exact ⟨hFinish, hValues⟩
    apply unwind_cleanup_spec env pushed released fuel index state (index - 1) (unwindParent index state history)
      terrainNode.root historyNode.root rowNode.root node.root true out0 out1 prepared staged hPrepared
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (by simp [prepared, unwindTailAux, hParentLength]) (by simp [prepared, unwindTailAux, hParentLength])
      (borrowed_root_ne_zero hTerrain) (borrowed_root_ne_zero hHistory) (owned_root_ne_zero hRow)
      hOldTerrain hOldHistory hOldRoot (by simp) (fun _ => hCall)
    intro nextAux hAuxLength hFinal33 hFinal35
    have hRoot32 : rowNode.root.toNat ≤ 4294967296 := by have := hOld.buffer.addressBound; omega
    refine hNext released (nextHeap.release rowNode) node nextAux staged hAuxLength hFinal33 (hFinal35.trans hPrepared35) ?_
      (hPushedBudget.released rowNode)
      (hCurrentTerrain.released rowNode hOld.buffer.rootBound hRoot32 hTerrainSep)
      (hCurrentHistory.released rowNode hOld.buffer.rootBound hRoot32 hHistorySep)
      (hOutput.released rowNode hOld.buffer.rootBound hRoot32 (word_regions_symm hOldNew))
      hNewTerrain hNewHistory (hKept.released rowNode hOld.buffer.rootBound hRoot32 (hTracked rfl)) hFreshOriginal
    exact nextHeap.release_at pushed rowNode hPushedHeap hOld.buffer.rootBound hOld.buffer.addressBound
      hOld.buffer.memoryBound hOld.buffer.fresh.2.2.1 hOld.below hOld.separated

#print axioms unwind_step_spec
end Project.Drone.Execution
