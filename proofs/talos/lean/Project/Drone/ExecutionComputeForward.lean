import Project.Drone.ExecutionComputeStart
import Project.Drone.ExecutionComputeHistoryCall
import Project.Drone.ExecutionInitial
import Project.Drone.ExecutionHistory

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 400000 in
theorem compute_forward_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (terrainNode : FreeNode) (terrain : Array UInt64) (aux : List Value) (s : Scratch)
    (remaining pageLimit : Nat) (hAux : aux.length = 30) (hPositive : 0 < terrain.size)
    (hTerrain : BorrowedWords heap store terrainNode terrain) (hHeap : heap.At store)
    (hBudget : Budget store heap
      (56 + (advanceCost 45 0 + (56 + (historyCost (terrain.size - 1) 0 + remaining)))) pageLimit)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (historyNode : FreeNode)
      (nextAux : List Value) (nextScratch : Scratch), nextAux.length = 30 →
      nextAux[18]? = some (.i64 historyNode.root) → nextAux[19]? = some (.i64 historyNode.root) →
      nextHeap.At final → Budget final nextHeap remaining pageLimit →
      BorrowedWords nextHeap final terrainNode terrain →
      nextHeap.OwnsWords final historyNode (buildHistory (terrain.size - 1) 1 terrain initial #[]) →
      PreservesWords heap store nextHeap final →
      wp Project.Drone.«module» rest Q final (computeFrame terrainNode.root nextAux nextScratch) env) :
    wp Project.Drone.«module» (computeAccept.take 86 ++ rest) Q store (computeFrame terrainNode.root aux s) env := by
  have hCode : computeAccept.take 86 = computeAccept.take 26 ++ emptyProgram 31 ++
      (computeAccept.drop 66).take 20 := rfl
  rw [hCode]
  simp only [List.append_assoc]
  let afterInitial := 56 + (historyCost (terrain.size - 1) 0 + remaining)
  have hInitial := initial_exact env store heap afterInitial pageLimit hHeap hBudget
  apply compute_start_spec env store terrainNode.root aux s terrain hAux hTerrain.values
    (fun final root => FreshArrayResult heap store initial afterInitial pageLimit final [.i64 root, .i64 root])
  · apply hInitial.mono
    intro final values h
    have hCopy := h
    obtain ⟨nextHeap, node, _, _, _, _, _, hValues⟩ := h
    exact ⟨node.root, hValues, by simpa only [hValues] using hCopy⟩
  intro initialized initialRoot prepared hLength hCount hIndex hOwner hPointer hPrev0 hPrev1 hInit
  rcases hInit with ⟨initialHeap, initialNode, hInitHeap, hInitBudget, hInitOwner, hInitPreserve, _, hRoots⟩
  have hRoot : initialRoot = initialNode.root := by simpa using hRoots
  subst initialRoot
  let staged := { s with counter := UInt64.ofNat terrain.size, value := 1, spare0 := terrainNode.root }
  have hBase : ([Value.i64 terrainNode.root].length + prepared.length) = 31 := by simp [hLength]
  rw [← hBase]
  apply empty_budget_spec env initialized initialHeap [.i64 terrainNode.root] prepared [] staged
    (historyCost (terrain.size - 1) 0 + remaining) pageLimit hInitHeap hInitBudget
  intro previous current capacity next hSeedHeap hSeedBudget hSeed hBorrow hOwned
  let seeded := emptyWordsStore initialHeap initialized
  let seededHeap := initialHeap.allocate 8
  let seed := allocatedNode initialHeap.top 8 initialHeap.nodes
  have hKeep : PreservesWords initialHeap initialized seededHeap seeded :=
    ⟨fun node words h => (hBorrow node words h).1, hOwned⟩
  have hTerr := (hBorrow terrainNode terrain (hInitPreserve.borrowed _ _ hTerrain)).1
  have hPrev := hOwned initialNode initial hInitOwner
  have hHistory := buildHistory_exact env seeded seededHeap (terrain.size - 1) 1 remaining pageLimit
    terrainNode initialNode seed terrain initial #[] hTerr (borrow_owned hPrev)
    (by rw [Project.Drone.Initial.initial_size]) hSeed hSeedHeap hSeedBudget (by omega)
    (hBorrow terrainNode terrain (hInitPreserve.borrowed _ _ hTerrain)).2
  apply compute_history_call_spec env seeded terrainNode.root initialNode.root seed.root (terrain.size - 1)
    prepared (emptyScratch staged seed.root previous current capacity next) hLength hCount hIndex hOwner hPointer hPrev0 hPrev1
    (fun final root => AppendResult seededHeap seeded terrainNode terrain
      (buildHistory (terrain.size - 1) 1 terrain initial #[]) (terrain.size - 1) remaining pageLimit final [.i64 root, .i64 root])
  · apply hHistory.mono
    intro final values h
    have hCopy := h
    obtain ⟨nextHeap, node, _, _, _, _, _, _, _, hValues⟩ := h
    exact ⟨node.root, hValues, by simpa only [hValues] using hCopy⟩
  intro final root nextAux hNextLength hHistory0 hHistory1 hResult
  rcases hResult with ⟨nextHeap, node, hFinalHeap, hFinalBudget, hFinalTerrain, hOutput, _, hPreserve, _, hValues⟩
  have hRoot : root = node.root := by simpa using hValues
  subst root
  exact hNext final nextHeap node nextAux _ hNextLength hHistory0 hHistory1 hFinalHeap hFinalBudget hFinalTerrain hOutput
    (hInitPreserve.trans (hKeep.trans hPreserve))

#print axioms compute_forward_spec
end Project.Drone.Execution
