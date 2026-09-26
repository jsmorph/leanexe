import Project.Drone.ExecutionUnwindPrepare
import Project.Drone.ExecutionUnwindPush

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
theorem unwind_two_push_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (fuel index state remaining pageLimit : Nat) (terrainNode rowNode : FreeNode)
    (terrain row : Array UInt64) (history out0 out1 : UInt64) (tracked : Bool)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 36) (hState : state < UInt64.size)
    (hTerrain : BorrowedWords heap store terrainNode terrain) (hIndex : index < terrain.size)
    (hRow : heap.OwnsWords store rowNode row) (hHeap : heap.At store)
    (hBudget : Budget store heap (pushCost row.size + (pushCost (row.size + 1) + remaining)) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (node : FreeNode) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 36 → nextAux[35]? = aux[35]? → nextHeap.At final → Budget final nextHeap remaining pageLimit →
      nextHeap.OwnsWords final node ((row.push (speed state)).push (altitude (floorAt terrain index) state)) →
      PreservesWords heap store nextHeap final → SeparateWords heap store node →
      wp Project.Drone.«module» rest Q final
        { unwindFrame fuel index state terrainNode.root history rowNode.root tracked out0 out1 nextAux nextScratch with
          values := [.i64 node.root] } env) :
    wp Project.Drone.«module» ((unwindLoopBody.drop 7).take 169 ++ rest) Q store
      (unwindFrame fuel index state terrainNode.root history rowNode.root tracked out0 out1 aux s) env := by
  have hCode : (unwindLoopBody.drop 7).take 169 = (unwindLoopBody.drop 7).take 11 ++
      WordArrayPush.program 51 ++ (unwindLoopBody.drop 85).take 24 ++ WordArrayPush.program 51 := rfl
  rw [hCode]
  simp only [List.append_assoc]
  apply unwind_speed_spec env store fuel index state terrainNode.root history rowNode.root tracked
    out0 out1 aux s hAux hState
  intro speedAux hSpeedLength hSpeed35
  let staged := { s with source := rowNode.root, value := speed state }
  apply unwind_push_spec env store heap fuel index state terrainNode.root history rowNode.root tracked
    out0 out1 speedAux staged rowNode row (pushCost (row.size + 1) + remaining) pageLimit
    hSpeedLength rfl (borrow_owned hRow) hHeap hBudget
  intro first previous current capacity next hFirstHeap hFirstBudget hFirstOutput hKeep _
  let firstHeap := heap.allocate (pushNeed row.size)
  let firstNode := allocatedNode heap.top (pushNeed row.size) heap.nodes
  let firstScratch := pushedScratch staged row.size firstNode.root previous current capacity next
  apply unwind_altitude_spec env first fuel index state terrainNode.root history rowNode.root firstNode.root tracked
    out0 out1 speedAux firstScratch terrain hSpeedLength (hKeep.borrowed _ _ hTerrain).values hIndex hState
  intro altitudeAux hAltitudeLength hAltitude35
  apply unwind_push_spec env first firstHeap fuel index state terrainNode.root history rowNode.root tracked
    out0 out1 altitudeAux { firstScratch with source := firstNode.root, value := altitude (floorAt terrain index) state }
    firstNode (row.push (speed state)) remaining pageLimit hAltitudeLength rfl (borrow_owned hFirstOutput)
    hFirstHeap (by simpa only [Array.size_push] using hFirstBudget)
  intro final p2 c2 cap2 n2 hFinalHeap hFinalBudget hOutput hPreserve hFresh
  refine hNext final _ _ altitudeAux _ hAltitudeLength (hAltitude35.trans hSpeed35) hFinalHeap hFinalBudget hOutput (hKeep.trans hPreserve) ?_
  intro saved words hSaved
  exact hFresh saved words (hKeep.borrowed saved words hSaved)

#print axioms unwind_two_push_spec
end Project.Drone.Execution
