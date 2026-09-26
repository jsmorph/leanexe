import Project.Drone.ExecutionAdvanceInvariant

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxHeartbeats 600000 in
set_option maxRecDepth 32768 in
theorem advanceLoop_exact (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (r0 r1 : UInt64) (last : Bool) (previousNode rowNode : FreeNode) (previous row : Array UInt64)
    (count target remaining pageLimit : Nat)
    (hPrevious : BorrowedWords initialHeap initial previousNode previous)
    (hRow : initialHeap.OwnsWords initial rowNode row) (hHeap : initialHeap.At initial)
    (hBudget : Budget initial initialHeap (advanceCost count row.size + remaining) pageLimit)
    (hRange : 135 ≤ previous.size) (hTarget : target + count < UInt64.size)
    (hSeparate : regionsDisjoint previousNode.region rowNode.region) :
    TerminatesWith env Project.Drone.«module» 18 initial
      [.i64 rowNode.root, .i64 rowNode.root, .i64 previousNode.root, .i64 previousNode.root,
        .i64 (if last then 1 else 0), .i64 r1, .i64 r0,
        .i64 (UInt64.ofNat target), .i64 (UInt64.ofNat count)]
      (AdvanceResult initialHeap initial previousNode previous (advanceLoop count target r0 r1 last previous row)
        count remaining pageLimit) := by
  have hCount : count < UInt64.size := by omega
  apply advanceLoop_entry env initial r0 r1 last previousNode.root rowNode.root count target
  change wp Project.Drone.«module» (.block 0 0 [.loop 0 0 advanceLoopBody] :: _) _ initial _ env
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := advanceInv initialHeap initial r0 r1 last previousNode previous
      (advanceLoop count target r0 r1 last previous row) count (target + count) remaining pageLimit)
    (μ := appendMeasure)
  · refine ⟨initialHeap, rowNode, row, count, target, false, 0, 0,
      List.replicate 38 (.i64 0), zeroPushScratch, rfl, rfl, le_rfl, rfl, ?_,
      hHeap, hBudget, hPrevious, hRow, hSeparate, PreservesWords.refl _ _, ?_, rfl⟩
    · simp
    · simp
  · rintro store frame ⟨heap, node, currentRow, fuel, index, tracked, resultOwner, resultPointer,
      aux, scratch, rfl, hAux, hFuelBound, hBound, hTracking, hCurrentHeap, hCurrentBudget,
      hCurrentPrevious, hCurrentRow, hCurrentSeparate, hPreserve, hTracked, hExpected⟩
    have hFuel : fuel < UInt64.size := lt_of_le_of_lt hFuelBound hCount
    change wp Project.Drone.«module» (FuelGuard.program 0 13 ++ _) _ store _ env
    refine FuelGuard.program_spec 0 13 _ _ _ _ (UInt64.ofNat fuel) 0 rfl rfl
      (by simp [advanceFrame, Locals.get, Scratch.words, hAux]) _ _ ?_
    cases fuel with
    | zero =>
      rw [if_pos (by simp)]
      simp only [advanceLoop] at hExpected
      simp only [advanceCost, Nat.zero_add] at hCurrentBudget
      rw [hExpected] at hCurrentRow
      wp_advance_frame [hAux, func18Def]
      refine wp_iff_cons rfl ?_
      simp
      wp_advance_frame [hAux, func18Def]
      refine ⟨heap, node, hCurrentHeap, hCurrentBudget, hCurrentPrevious, hCurrentRow,
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
      change wp Project.Drone.«module» (advanceLoopBody.drop 7) _ store _ env
      apply advance_step_spec env store initial heap initialHeap fuel index
        (advanceCost fuel (currentRow.size + 3) + remaining) pageLimit r0 r1 last previousNode node
        previous currentRow tracked resultOwner resultPointer aux scratch hAux (by omega)
        hCurrentPrevious hCurrentRow hCurrentHeap
        (by simpa only [advanceCost, Nat.add_assoc] using hCurrentBudget) hRange
        hCurrentSeparate hPreserve hTracked
      intro final nextHeap nextNode nextAux nextScratch hLength hFinalHeap hFinalBudget
        hFinalPrevious hFinalRow hFinalSeparate hFinalPreserve hFinalFresh
      constructor
      · refine ⟨nextHeap, nextNode,
          ((currentRow.push (advanceChoice r0 r1 last previous index).time).push
            (advanceChoice r0 r1 last previous index).excess).push (advanceChoice r0 r1 last previous index).parent,
          fuel, index + 1, true, resultOwner, resultPointer, nextAux, nextScratch, rfl, hLength,
          by omega, by omega, ?_, hFinalHeap, ?_, hFinalPrevious, hFinalRow,
          hFinalSeparate, hFinalPreserve, fun _ => hFinalFresh, ?_⟩
        · simp only [true_iff]; omega
        · simpa only [Array.size_push, Nat.add_assoc] using hFinalBudget
        · simpa only [advanceLoop, advanceChoice] using hExpected
      · change (UInt64.ofNat fuel).toNat < (UInt64.ofNat (fuel + 1)).toNat
        rw [UInt64.toNat_ofNat_of_lt' (show fuel < UInt64.size by omega),
          UInt64.toNat_ofNat_of_lt' hFuel]
        omega

#print axioms advanceLoop_exact
end Project.Drone.Execution
