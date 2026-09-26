import Project.Drone.ExecutionHistoryRead
import Project.Drone.ExecutionHistoryLayer
import Project.Drone.ExecutionHistoryAppendCall
import Project.Drone.ExecutionHistoryTail
import Project.Drone.ExecutionAppend
import Project.Drone.Selection
import Project.Drone.ExecutionWordBounds

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

def historyLayer (index : Nat) (terrain previous : Array UInt64) : Array UInt64 :=
  advance (floorAt terrain (index - 1)) (floorAt terrain index) (index + 1 == terrain.size) previous

set_option maxRecDepth 32768 in
theorem history_step_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel index remaining pageLimit : Nat) (terrainNode previousNode historyNode : FreeNode)
    (terrain previous history : Array UInt64) (out0 out1 : UInt64) (aux : List Value) (s : Scratch)
    (hAux : aux.length = 44) (hIndex : index < terrain.size)
    (hTerrain : BorrowedWords heap store terrainNode terrain)
    (hPrevious : BorrowedWords heap store previousNode previous) (hRange : 135 ≤ previous.size)
    (hHistory : heap.OwnsWords store historyNode history) (hHeap : heap.At store)
    (hBudget : Budget store heap (56 + (advanceCost 45 0 + (appendCost 45 history.size + remaining))) pageLimit)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (layerNode nextNode : FreeNode)
      (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 44 → nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final layerNode (historyLayer index terrain previous) →
      nextHeap.OwnsWords final nextNode (appendParents 45 0 (historyLayer index terrain previous) history) →
      PreservesWords heap store nextHeap final → SeparateWords heap store nextNode →
      Q (.Break 0 final (historyFrame fuel (index + 1) terrainNode.root layerNode.root nextNode.root
        out0 out1 nextAux nextScratch))) :
    wp Project.Drone.«module» (historyLoopBody.drop 7) Q store
      (historyFrame (fuel + 1) index terrainNode.root previousNode.root historyNode.root out0 out1 aux s) env := by
  have hCode : historyLoopBody.drop 7 = (historyLoopBody.drop 7).take 62 ++
      (historyLoopBody.drop 69).take 61 ++ (historyLoopBody.drop 130).take 47 ++ historyLoopBody.drop 177 := rfl
  rw [hCode]
  apply history_read_spec env store (fuel + 1) index terrainNode.root previousNode.root historyNode.root out0 out1
    aux s terrain hAux hTerrain.values hIndex
  intro prepared staged hPrepared hCount hZero hR0 hR1 hLast hOwner hPointer
  apply history_layer_spec env store heap (fuel + 1) index (appendCost 45 history.size + remaining) pageLimit
    terrainNode.root historyNode.root out0 out1 _ _ _ previousNode previous prepared staged
    hPrepared hCount hZero hR0 hR1 hLast hOwner hPointer hPrevious hRange hHeap hBudget
  intro advanced layerHeap layerNode layerAux layerScratch hLayerLength hLayer0 hLayer1 hLayerHeap hLayerBudget
    hLayer hKeep hFresh
  have hLayerSize : (historyLayer index terrain previous).size = 135 :=
    Project.Drone.Selection.advance_size _ _ _ _
  have hAppend := appendParents_exact env advanced layerHeap layerNode historyNode
    (historyLayer index terrain previous) history 45 0 remaining pageLimit (borrow_owned hLayer)
    (hKeep.owned _ _ hHistory) hLayerHeap hLayerBudget (by rw [hLayerSize])
    (word_regions_symm (hFresh historyNode history (borrow_owned hHistory)))
  let P : Store Unit → UInt64 → Prop := fun final root =>
    ∃ nextHeap node, node.root = root ∧ nextHeap.At final ∧ Budget final nextHeap remaining pageLimit ∧
      nextHeap.OwnsWords final layerNode (historyLayer index terrain previous) ∧
      nextHeap.OwnsWords final node (appendParents 45 0 (historyLayer index terrain previous) history) ∧
      PreservesWords heap store nextHeap final ∧ SeparateWords heap store node
  have hCall : TerminatesWith env Project.Drone.«module» 21 advanced
      [.i64 historyNode.root, .i64 historyNode.root, .i64 layerNode.root, .i64 layerNode.root, .i64 0, .i64 45]
      (fun final values => ∃ root : UInt64, values = [.i64 root, .i64 root] ∧ P final root) := by
    apply hAppend.mono
    rintro final values ⟨nextHeap, node, hFinalHeap, hFinalBudget, _, hOutput, _, hPreserve, hFreshOutput, rfl⟩
    refine ⟨node.root, rfl, nextHeap, node, rfl, hFinalHeap, hFinalBudget,
      hPreserve.owned _ _ hLayer, hOutput, hKeep.trans hPreserve, ?_⟩
    intro saved words hSaved
    exact hFreshOutput (by decide) saved words (hKeep.borrowed saved words hSaved)
  have hIndex64 : index + 1 < UInt64.size := by have := hTerrain.values.size_lt; omega
  apply history_append_call_spec env advanced (fuel + 1) index terrainNode.root previousNode.root historyNode.root
    out0 out1 layerNode.root layerAux layerScratch hLayerLength hIndex64 hLayer0 hLayer1 P hCall
  rintro final root nextAux nextScratch hLength hNextIndex hTerrain0 hTerrain1 hNextLayer0 hNextLayer1 hRoot0 hRoot1
    ⟨nextHeap, node, rfl, hFinalHeap, hFinalBudget, hFinalLayer, hOutput, hPreserve, hFreshOutput⟩
  have hTerrainNonzero : terrainNode.root ≠ 0 := borrowed_root_ne_zero hTerrain
  have hLayerNonzero : layerNode.root ≠ 0 := owned_root_ne_zero hFinalLayer
  have hOutputNonzero : node.root ≠ 0 := owned_root_ne_zero hOutput
  apply history_tail_spec env final fuel index terrainNode.root previousNode.root historyNode.root out0 out1
    layerNode.root node.root nextAux nextScratch hLength hNextIndex hTerrain0 hTerrain1 hNextLayer0 hNextLayer1
    hRoot0 hRoot1 hTerrainNonzero hLayerNonzero hOutputNonzero
  intro finalAux finalScratch hAuxLength
  exact hNext final nextHeap layerNode node finalAux finalScratch hAuxLength hFinalHeap hFinalBudget
    hFinalLayer hOutput hPreserve hFreshOutput

#print axioms history_step_spec
end Project.Drone.Execution
