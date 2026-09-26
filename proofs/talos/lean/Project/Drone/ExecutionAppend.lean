import Project.Drone.ExecutionAppendInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxHeartbeats 600000 in
set_option maxRecDepth 32768 in
theorem appendParents_exact (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (layerNode historyNode : FreeNode) (layer history : Array UInt64) (count state remaining pageLimit : Nat)
    (hLayer : BorrowedWords initialHeap initial layerNode layer)
    (hHistory : initialHeap.OwnsWords initial historyNode history) (hHeap : initialHeap.At initial)
    (hBudget : Budget initial initialHeap (appendCost count history.size + remaining) pageLimit)
    (hRange : 3 * (state + count) ≤ layer.size)
    (hSeparate : regionsDisjoint layerNode.region historyNode.region) :
    TerminatesWith env Project.Drone.«module» 21 initial
      [.i64 historyNode.root, .i64 historyNode.root, .i64 layerNode.root, .i64 layerNode.root,
        .i64 (UInt64.ofNat state), .i64 (UInt64.ofNat count)]
      (AppendResult initialHeap initial layerNode layer (appendParents count state layer history)
        count remaining pageLimit) := by
  have hCount : count < UInt64.size := by have := hLayer.values.size_lt; omega
  apply appendParents_entry env initial layerNode.root historyNode.root count state
  change wp Project.Drone.«module» (.block 0 0 [.loop 0 0 appendBody] :: _) _ initial _ env
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := appendInv initialHeap initial layerNode layer (appendParents count state layer history)
      count (state + count) remaining pageLimit) (μ := appendMeasure)
  · refine ⟨initialHeap, historyNode, history, count, state, false, 0, 0,
      List.replicate 14 (.i64 0), zeroPushScratch, 0, rfl, rfl, le_rfl, rfl, ?_,
      hHeap, hBudget, hLayer, hHistory, hSeparate, PreservesWords.refl _ _, ?_, rfl⟩
    · simp
    · simp
  · rintro store frame ⟨heap, node, row, fuel, index, tracked, resultOwner, resultPointer,
      aux, scratch, extra, rfl, hAux, hFuelBound, hBound, hTracking, hCurrentHeap, hCurrentBudget,
      hCurrentLayer, hCurrentHistory, hCurrentSeparate, hPreserve, hTracked, hExpected⟩
    have hFuel : fuel < UInt64.size := lt_of_le_of_lt hFuelBound hCount
    change wp Project.Drone.«module» (FuelGuard.program 0 10 ++ _) _ store _ env
    refine FuelGuard.program_spec 0 10 _ _ _ _ (UInt64.ofNat fuel) 0 rfl rfl
      (by simp [appendFrame, Locals.get, Scratch.words, hAux]) _ _ ?_
    cases fuel with
    | zero =>
      rw [if_pos (by simp)]
      simp only [appendParents] at hExpected
      simp only [appendCost, Nat.zero_add] at hCurrentBudget
      rw [hExpected] at hCurrentHistory
      wp_append_frame [hAux, func21Def]
      refine wp_iff_cons rfl ?_
      simp
      wp_append_frame [hAux, func21Def]
      refine ⟨heap, node, hCurrentHeap, hCurrentBudget, hCurrentLayer, hCurrentHistory,
        hCurrentSeparate, hPreserve, ?_, rfl⟩
      intro hPositive
      exact hTracked (hTracking.mpr hPositive)
    | succ fuel =>
      have hNonzero : UInt64.ofNat (fuel + 1) ≠ 0 := by
        intro h
        have hn := congrArg UInt64.toNat h
        rw [UInt64.toNat_ofNat_of_lt' hFuel, UInt64.toNat_zero] at hn
        omega
      rw [if_neg (by simpa only [ne_eq, eq_self_iff_true, not_true_eq_false, or_false] using hNonzero)]
      change wp Project.Drone.«module» (appendBody.drop 7) _ store _ env
      have hRead : 3 * index + 2 < layer.size := by omega
      apply append_step_spec env store initial heap initialHeap fuel index
        (appendCost fuel (row.size + 1) + remaining) pageLimit layerNode node layer row tracked
        resultOwner resultPointer aux scratch extra hAux hFuel hCurrentLayer hCurrentHistory
        hCurrentHeap (by simpa only [appendCost, Nat.add_assoc] using hCurrentBudget) hRead
        hCurrentSeparate hPreserve hTracked
      intro final nextHeap nextNode nextAux nextScratch nextExtra hLength hFinalHeap hFinalBudget
        hFinalLayer hFinalHistory hFinalSeparate hFinalPreserve hFinalFresh
      constructor
      · refine ⟨nextHeap, nextNode, row.push layer[3 * index + 2], fuel, index + 1, true,
          resultOwner, resultPointer, nextAux, nextScratch, nextExtra, rfl, hLength,
          by omega, by omega, ?_, hFinalHeap, ?_, hFinalLayer, hFinalHistory,
          hFinalSeparate, hFinalPreserve, fun _ => hFinalFresh, ?_⟩
        · simp only [eq_self_iff_true, true_iff]; omega
        · simpa only [Array.size_push] using hFinalBudget
        · simpa only [appendParents, getElem!_pos layer (3 * index + 2) hRead] using hExpected
      · change (UInt64.ofNat fuel).toNat < (UInt64.ofNat (fuel + 1)).toNat
        rw [UInt64.toNat_ofNat_of_lt' (show fuel < UInt64.size by omega),
          UInt64.toNat_ofNat_of_lt' hFuel]
        omega

#print axioms appendParents_exact
end Project.Drone.Execution
