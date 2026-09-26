import Project.Drone.ExecutionUnwindInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 400000 in
theorem unwind_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (count index state remaining pageLimit : Nat) (terrainNode historyNode rowNode : FreeNode)
    (terrain history row : Array UInt64) (out0 out1 : UInt64) (aux : List Value) (s : Scratch)
    (hAux : aux.length = 36) (hCount : count ≤ index + 1) (hIndex : index < terrain.size) (hState : state < 45)
    (hRange : index * 45 ≤ history.size) (hParents : ∀ j, j < history.size → history[j]!.toNat < 45)
    (hTerrain : BorrowedWords initialHeap initial terrainNode terrain)
    (hHistory : BorrowedWords initialHeap initial historyNode history)
    (hRow : initialHeap.OwnsWords initial rowNode row) (hHeap : initialHeap.At initial)
    (hBudget : Budget initial initialHeap (unwindCost count row.size + remaining) pageLimit)
    (hTerrainSep : regionsDisjoint terrainNode.region rowNode.region)
    (hHistorySep : regionsDisjoint historyNode.region rowNode.region)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (heap : Heap) (node : FreeNode) (output : Array UInt64)
      (finalIndex finalState : Nat) (tracked : Bool) (nextOut0 nextOut1 : UInt64)
      (nextAux : List Value) (nextScratch : Scratch), nextAux.length = 36 →
      heap.At final → Budget final heap (reverseCost output.size + remaining) pageLimit →
      heap.OwnsWords final node output → PreservesWords initialHeap initial heap final →
      (0 < count → SeparateWords initialHeap initial node) → output.size = row.size + 2 * count →
      output.reverse = unwind count index state terrain history row →
      wp Project.Drone.«module» rest Q final
        (unwindFrame 0 finalIndex finalState terrainNode.root historyNode.root node.root tracked
          nextOut0 nextOut1 nextAux nextScratch) env) :
    wp Project.Drone.«module» (.block 0 0 [.loop 0 0 unwindLoopBody] :: rest) Q initial
      (unwindFrame count index state terrainNode.root historyNode.root rowNode.root false out0 out1 aux s) env := by
  have hCount64 : count < UInt64.size := by have := hTerrain.values.size_lt; omega
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := unwindInv initialHeap initial terrainNode historyNode terrain history
      (unwind count index state terrain history row) count index (row.size + 2 * count) remaining pageLimit)
    (μ := appendMeasure)
  · exact ⟨initialHeap, rowNode, row, count, index, state, false, out0, out1, aux, s, rfl,
      hAux, le_rfl, le_rfl, hIndex, hCount, hState, by simp, hHeap, hBudget,
      hTerrain, hHistory, hRow, hTerrainSep, hHistorySep, PreservesWords.refl _ _, by simp, rfl, rfl⟩
  · rintro store frame ⟨heap, node, currentRow, fuel, currentIndex, currentState, tracked,
      currentOut0, currentOut1, currentAux, scratch, rfl, hLength, hFuelBound, hIndexBound, hCurrentIndex,
      hSteps, hCurrentState, hTracking, hCurrentHeap, hCurrentBudget, hCurrentTerrain, hCurrentHistory,
      hCurrentRow, hCurrentTerrainSep, hCurrentHistorySep, hPreserve, hTracked, hSize, hExpected⟩
    have hFuel64 : fuel < UInt64.size := lt_of_le_of_lt hFuelBound hCount64
    change wp Project.Drone.«module» (FuelGuard.program 0 14 ++ _) _ store _ env
    refine FuelGuard.program_spec 0 14 _ _ _ _ (UInt64.ofNat fuel) 0 rfl rfl
      (by simp [unwindFrame, unwindParams, Scratch.words, Locals.get, hLength]) _ _ ?_
    cases fuel with
    | zero =>
      rw [if_pos (by simp)]
      change currentRow.reverse = unwind count index state terrain history row at hExpected
      have hOutputSize : currentRow.size = row.size + 2 * count := by omega
      have hFresh : 0 < count → SeparateWords initialHeap initial node :=
        fun hPositive => hTracked (hTracking.mpr hPositive)
      simpa only [unwindFrame, unwindParams, List.take_zero, List.drop_zero, List.nil_append] using
        hNext store heap node currentRow currentIndex currentState tracked currentOut0 currentOut1
          currentAux scratch hLength hCurrentHeap hCurrentBudget hCurrentRow hPreserve hFresh hOutputSize hExpected
    | succ fuel =>
      have hNonzero : UInt64.ofNat (fuel + 1) ≠ 0 := by
        intro h
        have hn := congrArg UInt64.toNat h
        rw [UInt64.toNat_ofNat_of_lt' hFuel64, UInt64.toNat_zero] at hn
        omega
      rw [if_neg (by simpa only [ne_eq, eq_self_iff_true, not_true_eq_false, or_false] using hNonzero)]
      have hRead : 0 < currentIndex → (currentIndex - 1) * 45 + currentState < history.size := by
        intro hi
        omega
      have hNextState : unwindParent currentIndex currentState history < 45 := by
        by_cases hp : 0 < currentIndex
        · simpa only [unwindParent, hp, ↓reduceIte] using hParents _ (hRead hp)
        · simpa only [unwindParent, hp, ↓reduceIte] using hCurrentState
      change wp Project.Drone.«module» (unwindLoopBody.drop 7) _ store _ env
      apply unwind_step_spec env store initial heap initialHeap fuel currentIndex currentState
        (unwindCost fuel (currentRow.size + 2) + remaining) pageLimit terrainNode historyNode node
        terrain history currentRow tracked currentOut0 currentOut1 currentAux scratch hLength
        (by change currentState < 18446744073709551616; omega) hCurrentIndex hRead hCurrentTerrain hCurrentHistory
        hCurrentRow hCurrentHeap (by simpa only [unwindCost, Nat.add_assoc] using hCurrentBudget)
        hCurrentTerrainSep hCurrentHistorySep hPreserve hTracked
      intro final nextHeap nextNode nextAux nextScratch hNextLength hFinalHeap hFinalBudget hFinalTerrain hFinalHistory
        hOutput hFinalTerrainSep hFinalHistorySep hKeep hFresh
      constructor
      · refine ⟨nextHeap, nextNode, (currentRow.push (speed currentState)).push
          (altitude (floorAt terrain currentIndex) currentState), fuel, currentIndex - 1,
          unwindParent currentIndex currentState history, true, currentOut0, currentOut1, nextAux, nextScratch,
          rfl, hNextLength, by omega, by omega, by omega, by omega, hNextState, ?_, hFinalHeap, ?_,
          hFinalTerrain, hFinalHistory, hOutput, hFinalTerrainSep, hFinalHistorySep, hKeep, fun _ => hFresh, ?_, ?_⟩
        · simp only [true_iff]; omega
        · simpa only [Array.size_push, Nat.add_assoc] using hFinalBudget
        · simp only [Array.size_push]; omega
        · exact hExpected
      · change (UInt64.ofNat fuel).toNat < (UInt64.ofNat (fuel + 1)).toNat
        rw [UInt64.toNat_ofNat_of_lt' (show fuel < UInt64.size by omega), UInt64.toNat_ofNat_of_lt' hFuel64]
        omega

#print axioms unwind_loop_spec
end Project.Drone.Execution
