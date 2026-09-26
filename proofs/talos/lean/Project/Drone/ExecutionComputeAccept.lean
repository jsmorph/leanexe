import Project.Drone.ExecutionComputeForward
import Project.Drone.ExecutionComputeReconstruct
import Project.Drone.ExecutionComputeCost

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
theorem compute_accept_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (terrainNode : FreeNode) (terrain : Array UInt64) (aux : List Value) (s : Scratch)
    (remaining pageLimit : Nat) (hAux : aux.length = 30) (hPositive : 0 < terrain.size)
    (hTerrain : BorrowedWords heap store terrainNode terrain) (hHeap : heap.At store)
    (hBudget : Budget store heap (computeCost terrain.size + remaining) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 30 → nextScratch.target = root →
      FreshArrayResult heap store
        (unwind terrain.size (terrain.size - 1) 0 terrain (buildHistory (terrain.size - 1) 1 terrain initial #[]) #[])
        remaining pageLimit final [.i64 root, .i64 root] →
      wp Project.Drone.«module» rest Q final (computeFrame terrainNode.root nextAux nextScratch) env) :
    wp Project.Drone.«module» (computeAccept ++ rest) Q store (computeFrame terrainNode.root aux s) env := by
  rw [← List.take_append_drop 86 computeAccept, List.append_assoc]
  apply compute_forward_spec env store heap terrainNode terrain aux s
    (56 + (unwindCost terrain.size 0 + remaining)) pageLimit hAux hPositive hTerrain hHeap
    (by simpa only [computeCost, Nat.add_assoc] using hBudget)
  intro middle middleHeap historyNode prepared staged hLength hHistory0 hHistory1 hMiddleHeap hMiddleBudget
    hMiddleTerrain hHistory hKeep
  apply compute_reconstruct_spec env middle middleHeap terrainNode historyNode terrain prepared staged remaining pageLimit
    hLength hPositive hHistory0 hHistory1 hMiddleTerrain hHistory hMiddleHeap hMiddleBudget
  intro final root nextAux nextScratch hNextLength hTarget hResult
  apply hNext final root nextAux nextScratch hNextLength hTarget
  rcases hResult with ⟨nextHeap, node, hFinalHeap, hFinalBudget, hOutput, hPreserve, hFresh, hValues⟩
  refine ⟨nextHeap, node, hFinalHeap, hFinalBudget, hOutput, hKeep.trans hPreserve, ?_, hValues⟩
  intro saved words hSaved
  exact hFresh saved words (hKeep.borrowed saved words hSaved)

#print axioms compute_accept_spec
end Project.Drone.Execution
