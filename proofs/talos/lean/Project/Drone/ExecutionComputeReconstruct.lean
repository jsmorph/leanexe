import Project.Drone.ExecutionComputeUnwindPrepare
import Project.Drone.ExecutionComputeUnwindCall
import Project.Drone.ExecutionUnwind
import Project.Drone.ExecutionEmptyBudget
import Project.Drone.ParentBounds
import Project.Drone.History

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 400000 in
theorem compute_reconstruct_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (terrainNode historyNode : FreeNode) (terrain : Array UInt64) (aux : List Value) (s : Scratch)
    (remaining pageLimit : Nat) (hAux : aux.length = 30) (hPositive : 0 < terrain.size)
    (hHistory0 : aux[18]? = some (.i64 historyNode.root)) (hHistory1 : aux[19]? = some (.i64 historyNode.root))
    (hTerrain : BorrowedWords heap store terrainNode terrain)
    (hHistory : heap.OwnsWords store historyNode (buildHistory (terrain.size - 1) 1 terrain initial #[]))
    (hHeap : heap.At store) (hBudget : Budget store heap (56 + (unwindCost terrain.size 0 + remaining)) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 30 → nextScratch.target = root →
      FreshArrayResult heap store
        (unwind terrain.size (terrain.size - 1) 0 terrain (buildHistory (terrain.size - 1) 1 terrain initial #[]) #[])
        remaining pageLimit final [.i64 root, .i64 root] →
      wp Project.Drone.«module» rest Q final (computeFrame terrainNode.root nextAux nextScratch) env) :
    wp Project.Drone.«module» (computeAccept.drop 86 ++ rest) Q store (computeFrame terrainNode.root aux s) env := by
  have hCode : computeAccept.drop 86 = (computeAccept.drop 86).take 29 ++ emptyProgram 31 ++ computeAccept.drop 155 := rfl
  rw [hCode]
  simp only [List.append_assoc]
  apply compute_unwind_prepare_spec env store terrainNode.root historyNode.root aux s terrain hAux hHistory0 hHistory1
    hTerrain.values
  intro prepared hLength hCount hIndex hState hOwner hPointer hHist0 hHist1
  let staged := { s with counter := UInt64.ofNat terrain.size, value := 1, spare0 := terrainNode.root }
  have hBase : ([Value.i64 terrainNode.root].length + prepared.length) = 31 := by simp [hLength]
  rw [← hBase]
  apply empty_budget_spec env store heap [.i64 terrainNode.root] prepared [] staged
    (unwindCost terrain.size 0 + remaining) pageLimit hHeap hBudget
  intro previous current capacity next hSeedHeap hSeedBudget hSeed hBorrow hOwned
  let seeded := emptyWordsStore heap store
  let seededHeap := heap.allocate 8
  let seed := allocatedNode heap.top 8 heap.nodes
  have hKeep : PreservesWords heap store seededHeap seeded :=
    ⟨fun node words h => (hBorrow node words h).1, hOwned⟩
  have hTerr := (hBorrow terrainNode terrain hTerrain).1
  have hHist := hOwned historyNode _ hHistory
  have hRange := (Project.Drone.History.computed_history_valid terrain).1
  have hCall := unwind_exact env seeded seededHeap terrain.size (terrain.size - 1) 0 remaining pageLimit
    terrainNode historyNode seed terrain (buildHistory (terrain.size - 1) 1 terrain initial #[]) #[]
    hPositive (by omega) (by omega) (by decide) (by rw [hRange]; rfl)
    (Project.Drone.ParentBounds.computed_parent terrain) hTerr (borrow_owned hHist) hSeed hSeedHeap hSeedBudget
    (hBorrow terrainNode terrain hTerrain).2 (hBorrow historyNode _ (borrow_owned hHistory)).2
  apply compute_unwind_call_spec env seeded terrainNode.root historyNode.root seed.root terrain.size prepared
    (emptyScratch staged seed.root previous current capacity next) hLength hCount hIndex hState hOwner hPointer hHist0 hHist1
    (fun final root => FreshArrayResult seededHeap seeded
      (unwind terrain.size (terrain.size - 1) 0 terrain (buildHistory (terrain.size - 1) 1 terrain initial #[]) #[])
      remaining pageLimit final [.i64 root, .i64 root])
  · apply hCall.mono
    intro final values h
    have hCopy := h
    obtain ⟨nextHeap, node, _, _, _, _, _, hValues⟩ := h
    exact ⟨node.root, hValues, by simpa only [hValues] using hCopy⟩
  intro final root nextAux hNextLength hResult
  rcases hResult with ⟨nextHeap, node, hFinalHeap, hFinalBudget, hOutput, hPreserve, hFresh, hValues⟩
  apply hNext final root nextAux _ hNextLength rfl
  refine ⟨nextHeap, node, hFinalHeap, hFinalBudget, hOutput, hKeep.trans hPreserve, ?_, hValues⟩
  intro saved words hSaved
  exact hFresh saved words (hKeep.borrowed saved words hSaved)

#print axioms compute_reconstruct_spec
end Project.Drone.Execution
