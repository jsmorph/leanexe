import Project.Drone.ExecutionUnwindLoop
import Project.Drone.ExecutionUnwindReverse

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
theorem unwind_exact (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (count index state remaining pageLimit : Nat) (terrainNode historyNode rowNode : FreeNode)
    (terrain history row : Array UInt64) (hPositive : 0 < count)
    (hCount : count ≤ index + 1) (hIndex : index < terrain.size) (hState : state < 45)
    (hRange : index * 45 ≤ history.size) (hParents : ∀ j, j < history.size → history[j]!.toNat < 45)
    (hTerrain : BorrowedWords initialHeap initial terrainNode terrain)
    (hHistory : BorrowedWords initialHeap initial historyNode history)
    (hRow : initialHeap.OwnsWords initial rowNode row) (hHeap : initialHeap.At initial)
    (hBudget : Budget initial initialHeap (unwindCost count row.size + remaining) pageLimit)
    (hTerrainSep : regionsDisjoint terrainNode.region rowNode.region)
    (hHistorySep : regionsDisjoint historyNode.region rowNode.region) :
    TerminatesWith env Project.Drone.«module» 24 initial
      [.i64 rowNode.root, .i64 rowNode.root, .i64 historyNode.root, .i64 historyNode.root,
        .i64 terrainNode.root, .i64 terrainNode.root, .i64 (UInt64.ofNat state),
        .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat count)]
      (FreshArrayResult initialHeap initial (unwind count index state terrain history row) remaining pageLimit) := by
  apply unwind_entry
  change wp Project.Drone.«module» (.block 0 0 [.loop 0 0 unwindLoopBody] :: func24.drop 9) _ initial _ env
  apply unwind_loop_spec env initial initialHeap count index state remaining pageLimit terrainNode historyNode rowNode
    terrain history row 0 0 (List.replicate 36 (.i64 0)) zeroPushScratch rfl (by decide) (by decide)
    hCount hIndex hState hRange hParents hTerrain hHistory hRow hHeap hBudget hTerrainSep hHistorySep
  intro middle heap node output finalIndex finalState tracked out0 out1 aux scratch hAux h33 h35
    hMiddleHeap hMiddleBudget hOutput hKeep _ hSize hExpected
  apply unwind_reverse_spec env middle heap finalIndex finalState remaining pageLimit terrainNode.root historyNode.root
    node tracked out0 out1 aux scratch output hAux h33 h35 hOutput hMiddleHeap hMiddleBudget (by omega)
  rintro final values ⟨nextHeap, result, hFinalHeap, hFinalBudget, hResult, hPreserve, hFresh, hValues⟩
  rw [hExpected] at hResult
  refine ⟨nextHeap, result, hFinalHeap, hFinalBudget, hResult, hKeep.trans hPreserve, ?_, hValues⟩
  intro saved words hSaved
  exact hFresh saved words (hKeep.borrowed saved words hSaved)

#print axioms unwind_exact
end Project.Drone.Execution
