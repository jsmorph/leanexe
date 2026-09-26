import Project.Drone.ExecutionAdvanceChoice
import Project.Drone.ExecutionAdvancePrepare
import Project.Drone.ExecutionAdvancePushThree
import Project.Drone.ExecutionAdvanceRelease

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush LeanExe.Examples.Drone

set_option maxHeartbeats 400000 in
set_option maxRecDepth 32768 in
theorem advance_step_spec (env : HostEnv Unit) (store initial : Store Unit) (heap initialHeap : Heap)
    (fuel target remaining pageLimit : Nat) (r0 r1 : UInt64) (last : Bool)
    (previousNode rowNode : FreeNode) (previous row : Array UInt64) (tracked : Bool)
    (resultOwner resultPointer : UInt64) (aux : List Value) (s : Scratch)
    (hAux : aux.length = 38) (hTarget : target + 1 < UInt64.size)
    (hPrevious : BorrowedWords heap store previousNode previous) (hRow : heap.OwnsWords store rowNode row)
    (hHeap : heap.At store) (hBudget : Budget store heap (rowPushCost row.size + remaining) pageLimit)
    (hRange : 135 ≤ previous.size) (hSeparate : regionsDisjoint previousNode.region rowNode.region)
    (hPreserve : PreservesWords initialHeap initial heap store)
    (hTracked : tracked = true → SeparateWords initialHeap initial rowNode)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (nextHeap : Heap) (nextNode : FreeNode)
      (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 38 → nextHeap.At final → Budget final nextHeap remaining pageLimit →
      BorrowedWords nextHeap final previousNode previous →
      nextHeap.OwnsWords final nextNode
        (((row.push (advanceChoice r0 r1 last previous target).time).push
          (advanceChoice r0 r1 last previous target).excess).push (advanceChoice r0 r1 last previous target).parent) →
      regionsDisjoint previousNode.region nextNode.region →
      PreservesWords initialHeap initial nextHeap final → SeparateWords initialHeap initial nextNode →
      Q (.Break 0 final (advanceFrame fuel (target + 1) r0 r1 last previousNode.root previousNode.root
        nextNode.root nextNode.root nextNode.root resultOwner resultPointer nextAux nextScratch))) :
    wp Project.Drone.«module» (advanceLoopBody.drop 7) Q store
      (advanceFrame (fuel + 1) target r0 r1 last previousNode.root previousNode.root rowNode.root rowNode.root
        (if tracked then rowNode.root else 0) resultOwner resultPointer aux s) env := by
  have hBody : advanceLoopBody.drop 7 = (advanceLoopBody.drop 7).take 14 ++
      (advanceLoopBody.drop 21).take 28 ++ (advanceLoopBody.drop 49).take 211 ++
      advanceLoopBody.drop 260 := rfl
  rw [hBody]
  apply advance_choice_spec env store (fuel + 1) target r0 r1 last previousNode.root previousNode.root
    rowNode.root rowNode.root _ resultOwner resultPointer aux s previous hAux (by omega) hPrevious.values hRange
  intro choiceAux hChoiceLength hTime hExcess hParent
  apply advance_prepare_spec env store (fuel + 1) target r0 r1 last previousNode.root previousNode.root
    rowNode.root rowNode.root _ resultOwner resultPointer (advanceChoice r0 r1 last previous target).time
    choiceAux s hChoiceLength hTime hTarget
  let preparedAux := advancePreparedAux choiceAux target r0 r1 last previousNode.root previousNode.root rowNode.root
  let staged := advancePreparedScratch s target rowNode.root (advanceChoice r0 r1 last previous target).time
  apply advance_three_push_spec env store heap (fuel + 1) target r0 r1 last previousNode.root previousNode.root
    rowNode.root rowNode.root _ resultOwner resultPointer
    (advanceChoice r0 r1 last previous target).excess (advanceChoice r0 r1 last previous target).parent
    preparedAux staged rowNode row remaining pageLimit
    (by simp [preparedAux, advancePreparedAux, hChoiceLength])
    (by simpa [preparedAux, advancePreparedAux] using hExcess)
    (by simpa [preparedAux, advancePreparedAux] using hParent) rfl (borrow_owned hRow) hHeap hBudget
  intro final nextHeap node pushedAux nextScratch hLength hStable hFinalHeap hFinalBudget hOutput hKeep hFresh
  have hPreviousAfter := hKeep.borrowed previousNode previous hPrevious
  have hPreviousNew := hFresh previousNode previous hPrevious
  have hOldAfter := hKeep.owned rowNode row hRow
  have hOldNew := hFresh rowNode row (borrow_owned hRow)
  have hKept := hPreserve.trans hKeep
  have hFreshOriginal : SeparateWords initialHeap initial node := by
    intro saved words hSaved
    exact hFresh saved words (hPreserve.borrowed saved words hSaved)
  have hPreviousNonzero : previousNode.root ≠ 0 := by
    intro h; have := hPrevious.rootBound; rw [h] at this; contradiction
  have hOldNonzero : rowNode.root ≠ 0 := by
    intro h; have := hRow.buffer.rootBound; rw [h] at this; contradiction
  have hOldNewRoot : rowNode.root ≠ node.root :=
    word_regions_ne hRow.buffer.rootBound hOutput.buffer.rootBound hOldNew
  have hOldPrevious : rowNode.root ≠ previousNode.root :=
    Ne.symm (word_regions_ne hPrevious.rootBound hRow.buffer.rootBound hSeparate)
  have hT : pushedAux[16]? = some (.i64 (UInt64.ofNat (target + 1))) := by
    rw [hStable 16 (by decide) (by decide)]; simp [preparedAux, advancePreparedAux, hChoiceLength]
  have h0 : pushedAux[17]? = some (.i64 r0) := by
    rw [hStable 17 (by decide) (by decide)]; simp [preparedAux, advancePreparedAux, hChoiceLength]
  have h1 : pushedAux[18]? = some (.i64 r1) := by
    rw [hStable 18 (by decide) (by decide)]; simp [preparedAux, advancePreparedAux, hChoiceLength]
  have hL : pushedAux[19]? = some (.i64 (if last then 1 else 0)) := by
    rw [hStable 19 (by decide) (by decide)]; simp [preparedAux, advancePreparedAux, hChoiceLength]
  have hO : pushedAux[20]? = some (.i64 previousNode.root) := by
    rw [hStable 20 (by decide) (by decide)]; simp [preparedAux, advancePreparedAux, hChoiceLength]
  have hP : pushedAux[21]? = some (.i64 previousNode.root) := by
    rw [hStable 21 (by decide) (by decide)]; simp [preparedAux, advancePreparedAux, hChoiceLength]
  cases tracked with
  | false =>
    apply advance_tail_zero_spec env final fuel target r0 r1 last previousNode.root previousNode.root
      rowNode.root rowNode.root resultOwner resultPointer node.root pushedAux nextScratch hLength
      hPreviousNonzero hT h0 h1 hL hO hP
    intro nextAux hAuxLength
    exact hNext final nextHeap node nextAux nextScratch hAuxLength hFinalHeap hFinalBudget
      hPreviousAfter hOutput hPreviousNew hKept hFreshOriginal
  | true =>
    have hRelease := release_words_exact env final nextHeap rowNode row hFinalHeap hOldAfter
    let released := nextHeap.releaseStore final rowNode
    have hReleaseExact : TerminatesWith env Project.Drone.«module» 29 final [.i64 rowNode.root]
        (fun finish values => finish = released ∧ values = []) := by
      apply hRelease.mono
      rintro finish values ⟨hValues, hFinish, _⟩
      exact ⟨hFinish, hValues⟩
    apply advance_tail_release_spec env final released fuel target r0 r1 last previousNode.root previousNode.root
      rowNode.root rowNode.root rowNode.root resultOwner resultPointer node.root pushedAux nextScratch
      hLength hPreviousNonzero hOldNonzero hOldNewRoot hOldPrevious hT h0 h1 hL hO hP hReleaseExact
    intro nextAux hAuxLength
    have hRoot32 : rowNode.root.toNat ≤ 4294967296 := by have := hOldAfter.buffer.addressBound; omega
    apply hNext released (nextHeap.release rowNode) node nextAux nextScratch hAuxLength
    · exact nextHeap.release_at final rowNode hFinalHeap hOldAfter.buffer.rootBound
        hOldAfter.buffer.addressBound hOldAfter.buffer.memoryBound hOldAfter.buffer.fresh.2.2.1
        hOldAfter.below hOldAfter.separated
    · exact hFinalBudget.released rowNode
    · exact hPreviousAfter.released rowNode hOldAfter.buffer.rootBound hRoot32 hSeparate
    · exact hOutput.released rowNode hOldAfter.buffer.rootBound hRoot32 (word_regions_symm hOldNew)
    · exact hPreviousNew
    · exact hKept.released rowNode hOldAfter.buffer.rootBound hRoot32 (hTracked rfl)
    · exact hFreshOriginal

#print axioms advance_step_spec
end Project.Drone.Execution
