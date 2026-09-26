import Project.Drone.ExecutionAppendRead
import Project.Drone.ExecutionAppendRelease
import Project.Drone.ExecutionPreserveWords

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

set_option maxHeartbeats 400000 in
set_option maxRecDepth 32768 in
theorem append_step_spec (env : HostEnv Unit) (store initial : Store Unit) (heap initialHeap : Heap)
    (fuel state remaining pageLimit : Nat) (layerNode historyNode : FreeNode)
    (layer history : Array UInt64) (tracked : Bool) (resultOwner resultPointer : UInt64)
    (aux : List Value) (s : Scratch) (extra : UInt64)
    (hAux : aux.length = 14) (hFuel : fuel + 1 < UInt64.size)
    (hLayer : BorrowedWords heap store layerNode layer) (hHistory : heap.OwnsWords store historyNode history)
    (hHeap : heap.At store) (hBudget : Budget store heap (pushCost history.size + remaining) pageLimit)
    (hRead : 3 * state + 2 < layer.size) (hSeparate : regionsDisjoint layerNode.region historyNode.region)
    (hPreserve : PreservesWords initialHeap initial heap store)
    (hTracked : tracked = true → SeparateWords initialHeap initial historyNode)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (nextNode : FreeNode)
      (nextAux : List Value) (nextScratch : Scratch) (nextExtra : UInt64),
      nextAux.length = 14 → nextHeap.At final → Budget final nextHeap remaining pageLimit →
      BorrowedWords nextHeap final layerNode layer →
      nextHeap.OwnsWords final nextNode (history.push layer[3 * state + 2]) →
      regionsDisjoint layerNode.region nextNode.region →
      PreservesWords initialHeap initial nextHeap final → SeparateWords initialHeap initial nextNode →
      Q (.Break 0 final (appendFrame fuel (state + 1) layerNode.root layerNode.root
        nextNode.root nextNode.root nextNode.root resultOwner resultPointer nextAux nextScratch nextExtra))) :
    wp Project.Drone.«module» (appendBody.drop 7) Q store
      (appendFrame (fuel + 1) state layerNode.root layerNode.root historyNode.root historyNode.root
        (if tracked then historyNode.root else 0) resultOwner resultPointer aux s extra) env := by
  have hBody : appendBody.drop 7 = (appendBody.drop 7).take 48 ++
      WordArrayPush.program 25 ++ appendBody.drop 122 := rfl
  rw [hBody]
  apply append_read_spec env store (fuel + 1) state layerNode.root layerNode.root historyNode.root
    historyNode.root _ resultOwner resultPointer aux s extra layer hAux hLayer.values hRead
  rw [appendFrame_as_push]
  let staged := appendPreparedScratch s state layerNode.root historyNode.root layer[3 * state + 2]
  let saved := [.i64 0, .i64 (if tracked then historyNode.root else 0), .i64 resultOwner,
    .i64 resultPointer, .i64 0] ++ appendPreparedAux aux state layerNode.root layerNode.root historyNode.root
  let params : List Wasm.Value := [.i64 (UInt64.ofNat (fuel + 1)), .i64 (UInt64.ofNat state), .i64 layerNode.root,
    .i64 layerNode.root, .i64 historyNode.root, .i64 historyNode.root]
  have hStart : params.length + saved.length = 25 := by
    simp [params, saved, appendPreparedAux_length, hAux]
  change wp _ (WordArrayPush.program 25 ++ appendBody.drop 122) Q store
    (WordArrayPush.frame params saved [.i64 (UInt64.ofNat state)] staged) env
  rw [← hStart]
  apply word_push_budget_spec env store heap params saved [.i64 (UInt64.ofNat state)] staged
    historyNode history remaining pageLimit rfl (borrow_owned hHistory) hHeap hBudget
  intro final previous current capacity next hFinalHeap hFinalBudget hOutput hBorrow hOwned
  let allocatedHeap := heap.allocate (pushNeed history.size)
  let node := allocatedNode heap.top (pushNeed history.size) heap.nodes
  let nextScratch := pushedScratch staged history.size node.root previous current capacity next
  have hLayerAfter := (hBorrow layerNode layer hLayer).1
  have hLayerNew := (hBorrow layerNode layer hLayer).2
  have hOldAfter := hOwned historyNode history hHistory
  have hOldNew := (hBorrow historyNode history (borrow_owned hHistory)).2
  have hKeep : PreservesWords initialHeap initial allocatedHeap final :=
    hPreserve.trans ⟨fun node words h => (hBorrow node words h).1, hOwned⟩
  have hFresh : SeparateWords initialHeap initial node := by
    intro saved words hSaved
    exact (hBorrow saved words (hPreserve.borrowed saved words hSaved)).2
  have hLayerNonzero : layerNode.root ≠ 0 := by
    intro h; have := hLayer.rootBound; rw [h] at this; contradiction
  have hOldNonzero : historyNode.root ≠ 0 := by
    intro h; have := hHistory.buffer.rootBound; rw [h] at this; contradiction
  have hOldNewRoot : historyNode.root ≠ node.root :=
    word_regions_ne hHistory.buffer.rootBound hOutput.buffer.rootBound hOldNew
  have hOldLayer : historyNode.root ≠ layerNode.root :=
    Ne.symm (word_regions_ne hLayer.rootBound hHistory.buffer.rootBound hSeparate)
  change wp _ (appendBody.drop 122) Q final
    { appendFrame (fuel + 1) state layerNode.root layerNode.root historyNode.root historyNode.root
        (if tracked then historyNode.root else 0) resultOwner resultPointer
        (appendPreparedAux aux state layerNode.root layerNode.root historyNode.root)
        nextScratch (UInt64.ofNat state) with values := [.i64 node.root] } env
  cases tracked with
  | false =>
    apply append_tail_zero_spec env final fuel state layerNode.root layerNode.root historyNode.root
      historyNode.root resultOwner resultPointer node.root _ nextScratch (UInt64.ofNat state)
      (by simpa only [appendPreparedAux_length] using hAux) hFuel hLayerNonzero
      (by simp [appendPreparedAux, hAux]) (by simp [appendPreparedAux, hAux])
      (by simp [appendPreparedAux, hAux])
    intro nextAux hLength
    exact hNext final allocatedHeap node nextAux nextScratch (UInt64.ofNat state) hLength
      hFinalHeap hFinalBudget hLayerAfter hOutput hLayerNew hKeep hFresh
  | true =>
    have hRelease := release_words_exact env final allocatedHeap historyNode history hFinalHeap hOldAfter
    let released := allocatedHeap.releaseStore final historyNode
    have hReleaseExact : TerminatesWith env Project.Drone.«module» 29 final [.i64 historyNode.root]
        (fun finish values => finish = released ∧ values = []) := by
      apply hRelease.mono
      rintro finish values ⟨hValues, hFinish, _⟩
      exact ⟨hFinish, hValues⟩
    apply append_tail_release_spec env final released fuel state layerNode.root layerNode.root historyNode.root
      historyNode.root historyNode.root resultOwner resultPointer node.root _ nextScratch (UInt64.ofNat state)
      (by simpa only [appendPreparedAux_length] using hAux) hLayerNonzero hOldNonzero hOldNewRoot hOldLayer
      (by simp [appendPreparedAux, hAux]) (by simp [appendPreparedAux, hAux])
      (by simp [appendPreparedAux, hAux]) hReleaseExact
    intro nextAux hLength
    have hRoot32 : historyNode.root.toNat ≤ 4294967296 := by have := hOldAfter.buffer.addressBound; omega
    apply hNext released (allocatedHeap.release historyNode) node nextAux nextScratch (UInt64.ofNat state)
      hLength
    · exact allocatedHeap.release_at final historyNode hFinalHeap hOldAfter.buffer.rootBound
        hOldAfter.buffer.addressBound hOldAfter.buffer.memoryBound hOldAfter.buffer.fresh.2.2.1
        hOldAfter.below hOldAfter.separated
    · exact hFinalBudget.released historyNode
    · exact hLayerAfter.released historyNode hOldAfter.buffer.rootBound hRoot32 hSeparate
    · exact hOutput.released historyNode hOldAfter.buffer.rootBound hRoot32 (word_regions_symm hOldNew)
    · exact hLayerNew
    · exact hKeep.released historyNode hOldAfter.buffer.rootBound hRoot32 (hTracked rfl)
    · exact hFresh

#print axioms append_step_spec
end Project.Drone.Execution
