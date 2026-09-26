import Project.Drone.ExecutionHistoryInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 400000 in
theorem buildHistory_exact (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (count index remaining pageLimit : Nat) (terrainNode previousNode historyNode : FreeNode)
    (terrain previous history : Array UInt64)
    (hTerrain : BorrowedWords initialHeap initial terrainNode terrain)
    (hPrevious : BorrowedWords initialHeap initial previousNode previous) (hRange : 135 ≤ previous.size)
    (hHistory : initialHeap.OwnsWords initial historyNode history) (hHeap : initialHeap.At initial)
    (hBudget : Budget initial initialHeap (historyCost count history.size + remaining) pageLimit)
    (hBound : index + count ≤ terrain.size)
    (hSeparate : regionsDisjoint terrainNode.region historyNode.region) :
    TerminatesWith env Project.Drone.«module» 22 initial
      [.i64 historyNode.root, .i64 historyNode.root, .i64 previousNode.root, .i64 previousNode.root,
        .i64 terrainNode.root, .i64 0, .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat count)]
      (AppendResult initialHeap initial terrainNode terrain (buildHistory count index terrain previous history)
        count remaining pageLimit) := by
  have hCount : count < UInt64.size := by have := hTerrain.values.size_lt; omega
  apply history_entry
  change wp Project.Drone.«module» (.block 0 0 [.loop 0 0 historyLoopBody] :: _) _ initial _ env
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := historyInv initialHeap initial terrainNode terrain
      (buildHistory count index terrain previous history) count (index + count) remaining pageLimit)
    (μ := appendMeasure)
  · refine ⟨initialHeap, previousNode, historyNode, previous, history, count, index, 0, 0,
      List.replicate 44 (.i64 0), zeroPushScratch, rfl, rfl, le_rfl, rfl, hHeap, hBudget,
      hTerrain, hPrevious, hRange, hHistory, hSeparate, PreservesWords.refl _ _, ?_, rfl⟩
    intro h; omega
  · rintro store frame ⟨heap, currentPreviousNode, currentHistoryNode, currentPrevious, currentHistory,
      fuel, currentIndex, out0, out1, aux, scratch, rfl, hAux, hFuelBound, hCurrentBound,
      hCurrentHeap, hCurrentBudget, hCurrentTerrain, hCurrentPrevious, hCurrentRange, hCurrentHistory,
      hCurrentSeparate, hPreserve, hFresh, hExpected⟩
    have hFuel : fuel < UInt64.size := lt_of_le_of_lt hFuelBound hCount
    change wp Project.Drone.«module» (FuelGuard.program 0 13 ++ _) _ store _ env
    refine FuelGuard.program_spec 0 13 _ _ _ _ (UInt64.ofNat fuel) 0 rfl rfl
      (by simp [historyFrame, historyParams, Scratch.words, Locals.get, hAux]) _ _ ?_
    cases fuel with
    | zero =>
      rw [if_pos (by simp)]
      change currentHistory = buildHistory count index terrain previous history at hExpected
      simp only [historyCost, Nat.zero_add] at hCurrentBudget
      rw [hExpected] at hCurrentHistory
      wp_history_frame [hAux, func22Def]
      refine wp_iff_cons rfl ?_
      simp
      wp_history_frame [hAux, func22Def]
      exact ⟨heap, currentHistoryNode, hCurrentHeap, hCurrentBudget, hCurrentTerrain, hCurrentHistory,
        hCurrentSeparate, hPreserve, hFresh, rfl⟩
    | succ fuel =>
      have hNonzero : UInt64.ofNat (fuel + 1) ≠ 0 := by
        intro h
        have hn := congrArg UInt64.toNat h
        rw [UInt64.toNat_ofNat_of_lt' hFuel, UInt64.toNat_zero] at hn
        omega
      rw [if_neg (by simpa only [ne_eq, eq_self_iff_true, not_true_eq_false, or_false] using hNonzero)]
      change wp Project.Drone.«module» (historyLoopBody.drop 7) _ store _ env
      apply history_step_spec env store heap fuel currentIndex
        (historyCost fuel (currentHistory.size + 45) + remaining) pageLimit terrainNode
        currentPreviousNode currentHistoryNode terrain currentPrevious currentHistory out0 out1 aux scratch
        hAux (by omega) hCurrentTerrain hCurrentPrevious hCurrentRange hCurrentHistory hCurrentHeap
        (by simpa only [historyCost, Nat.add_assoc] using hCurrentBudget)
      intro final nextHeap layerNode node nextAux nextScratch hLength hFinalHeap hFinalBudget
        hLayer hOutput hKeep hFreshOutput
      constructor
      · refine ⟨nextHeap, layerNode, node, historyLayer currentIndex terrain currentPrevious,
          appendParents 45 0 (historyLayer currentIndex terrain currentPrevious) currentHistory,
          fuel, currentIndex + 1, out0, out1, nextAux, nextScratch, rfl, hLength, by omega, by omega,
          hFinalHeap, ?_, hKeep.borrowed _ _ hCurrentTerrain, borrow_owned hLayer, ?_, hOutput,
          hFreshOutput _ _ hCurrentTerrain, hPreserve.trans hKeep, ?_, ?_⟩
        · simpa only [Project.Drone.History.appendParents_size] using hFinalBudget
        · rw [historyLayer, Project.Drone.Selection.advance_size]
        · intro _ saved words hSaved
          exact hFreshOutput saved words (hPreserve.borrowed saved words hSaved)
        · exact hExpected
      · change (UInt64.ofNat fuel).toNat < (UInt64.ofNat (fuel + 1)).toNat
        rw [UInt64.toNat_ofNat_of_lt' (show fuel < UInt64.size by omega), UInt64.toNat_ofNat_of_lt' hFuel]
        omega

#print axioms buildHistory_exact
end Project.Drone.Execution
