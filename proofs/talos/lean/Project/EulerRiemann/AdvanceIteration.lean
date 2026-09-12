import Project.EulerRiemann.AdvanceReplace
import Project.ProofKit.BlockLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

local macro "advance_iteration_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [advanceTimeFrame, advanceScanFrame, advanceTrialFrame,
        advanceFinishedFrame, advanceContinuedFrame,
        List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, Bool.false_eq_true, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

def advanceIterationPost (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Control.Result) (spare limit measure : Nat) : Assertion Unit :=
  Project.ProofKit.BlockLoop.stepPost
    (advanceInvariant initial initialHeap n startTime expected spare limit)
    (fun store frame => ∃ heap, RetryStoreAt initial initialHeap store heap ∧
      AdvanceDone initial initialHeap n startTime expected spare limit store heap frame)
    (fun _ frame => advanceMeasure frame) measure

theorem advance_iteration_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n : Nat) (startTime : UInt64) (expected : Control.Result) (spare limit : Nat)
    (store : Store Unit) (frame : Locals) (hn : 2 ≤ n ∧ n ≤ 800) (hSuccess : expected.status = 0)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (hInv : advanceInvariant initial initialHeap n startTime expected spare limit store frame) :
    wp Project.EulerRiemann.«module» advanceLoop
      (advanceIterationPost initial initialHeap n startTime expected spare limit (advanceMeasure frame))
      store frame env := by
  obtain ⟨heap, hStore, hActive | hDone⟩ := hInv
  · obtain ⟨fuel, time, source, grid, tracked, hFrame, hSame, hEnough, hCurrent, hReserve⟩ := hActive
    have hFuel : fuel ≠ 0 := by
      intro hZero
      simp [hZero] at hEnough
    have hFuelNat := retryFuel_unfold fuel hFuel
    have hSourceSuccess : (Control.advance fuel.toNat n time grid).status = 0 := by
      rw [hSame]
      exact hSuccess
    have hParams := hFrame.params
    have hLocals := hFrame.locals
    have hValues := hFrame.values
    rcases frame with ⟨params, locals, values⟩
    dsimp only at hParams hLocals hValues ⊢
    subst params
    subst values
    let frame : Locals := ⟨[.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 source.root, .i64 source.root], locals, []⟩
    rw [advance_loop_parts, List.append_assoc]
    apply advance_active_guard_spec env store frame fuel n time source.root
      (if tracked then source.root else 0) 0 0 hFrame hFuel
    apply advance_time_spec env store frame hFrame.locals (by rw [hFrame.params]; rfl) hFrame.values
    by_cases hTime : time = Time.endTime
    · subst time
      have hTimeResult : expected.time = Time.endTime := by
        rw [← hSame, hFuelNat]
        simp [Control.advance]
      have hGridResult : expected.grid = grid := by
        rw [← hSame, hFuelNat]
        simp [Control.advance]
      dsimp only [frame]
      advance_iteration_peel
      apply advance_finish_spec env store (advanceTimeFrame frame) fuel n Time.endTime source.root
        (if tracked then source.root else 0) 0 0 false hFrame.time
      dsimp only [frame]
      advance_iteration_peel
      have hFinished := hFrame.time.finish
      simp only [advanceFinishedFrame, advanceTimeFrame] at hFinished
      have hReserved : heap.Reserved (gridCapacity n) (spare + 2) limit := by
        apply hReserve.mono
        cases tracked <;> simp
      change advanceInvariant _ _ _ _ _ _ _ _ _ ∧ _
      refine ⟨⟨heap, hStore, Or.inr ⟨fuel, source, tracked, ?_, hTimeResult, ?_, hReserved⟩⟩, ?_⟩
      · simpa only [hTimeResult] using hFinished
      · simpa only [hTimeResult, hGridResult] using hCurrent
      · dsimp only
        rw [hFinished.measure, hFrame.measure]
        simp
    · have hStep := Control.advance_success_step (fuel - 1).toNat n time grid hTime
        (by simpa only [hFuelNat] using hSourceSuccess)
      dsimp only at hStep
      have hScan := hStep.1
      have hTrialSuccess := hStep.2.1
      have hCurrentCap : limit ≤ store.memoryCap Project.EulerRiemann.«module» 0 * 65536 := by
        rw [hStore.cap]
        exact hCap
      let callSpare := spare + if tracked then 0 else 1
      have hTrialReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7)
          (callSpare + 2) limit := by
        cases tracked <;>
          simpa [gridCapacity, hCurrent.indexed.1, callSpare, Nat.add_assoc] using hReserve
      dsimp only [frame]
      advance_iteration_peel
      rw [advance_work_shape]
      refine advance_scan_spec env store (advanceTimeFrame frame) n fuel time source.root grid
        hFrame.time.params hFrame.time.locals hFrame.time.values hCurrent.owner.buffer.values _ _ ?_
      have hScanned := hFrame.time.scan { status := 0, alpha := (Traversal.scan grid).alpha }
      dsimp only [frame]
      advance_iteration_peel
      rw [advance_trial_shape]
      refine advance_trial_spec env store heap (advanceScanFrame (advanceTimeFrame frame) source.root
        { status := 0, alpha := (Traversal.scan grid).alpha })
        fuel source grid n time (Traversal.scan grid).alpha callSpare limit hScanned.params hScanned.locals
        hScanned.values (by simp [advanceScanFrame, advanceTimeFrame, frame, hLocals])
        hn hCurrent.indexed hStore.heapState hCurrent.owner hStore.pages hTrialReserve hLimit hCurrentCap
        hTrialSuccess _ _ ?_
      intro dt trial final finalHeap result hTrialStore hTrialOwner hTrialReserved hTrialCapacity hSeparated
      have hTrialFrame := hScanned.trial (Traversal.scan grid).alpha dt trial.dt result.root
      have hNextSame : Control.advance (fuel - 1).toNat n (IEEE64.add time trial.dt) trial.grid = expected := by
        exact hStep.2.2.trans (by simpa only [hFuelNat] using hSame)
      have hTrialValid := (Control.retry_success (dt.toNat + 1) n time dt grid hTrialSuccess).1
      have hDecrease := Time.remaining_decreases time trial.dt hTrialValid
      have hNextEnough : Time.endTime.toNat - (IEEE64.add time trial.dt).toNat < (fuel - 1).toNat := by
        omega
      have hNextIndexed := Control.retry_indexed (dt.toNat + 1) n time dt grid hCurrent.indexed hTrialSuccess
      have hNextCapacity : gridCapacity n ≤ result.capacity := by
        simpa only [gridCapacity, hCurrent.indexed.1] using hTrialCapacity
      have hNextReserved : finalHeap.Reserved (gridCapacity n) (spare + if tracked then 1 else 2) limit := by
        cases tracked <;>
          simpa [gridCapacity, hCurrent.indexed.1, callSpare, Nat.add_assoc] using hTrialReserved
      have hReplacement := hCurrent.replace hStore hTrialStore result trial.grid (IEEE64.add time trial.dt)
        spare limit hNextIndexed hTrialOwner hNextCapacity hSeparated hNextReserved
      have hSource : source.root ≠ 0 := by
        intro hZero
        have hRoot := hCurrent.owner.buffer.rootBound
        simp [hZero] at hRoot
      have hDifferent := freeNode_roots_ne source result (hSeparated source grid hCurrent.owner)
      dsimp only [frame]
      advance_iteration_peel
      apply advance_continue_spec env final finalHeap
        (advanceScanFrame (advanceTimeFrame frame) source.root
          { status := 0, alpha := (Traversal.scan grid).alpha }) fuel source grid
        n time (Traversal.scan grid).alpha dt trial.dt result.root tracked
        hScanned.params hScanned.locals hScanned.tracker hSource hDifferent hTrialStore.heapState
        (hTrialStore.held source grid hCurrent.owner)
      dsimp only [frame]
      advance_iteration_peel
      have hNextFrame := hTrialFrame.continued (IEEE64.add time trial.dt) result.root
      simp only [advanceContinuedFrame, advanceTrialFrame, advanceScanFrame, advanceTimeFrame] at hNextFrame
      change advanceInvariant _ _ _ _ _ _ _ _ _ ∧ _
      refine ⟨⟨_, hReplacement.1, Or.inl ⟨fuel - 1, IEEE64.add time trial.dt, result, trial.grid, true,
        hNextFrame, hNextSame, hNextEnough, hReplacement.2.1, hReplacement.2.2⟩⟩, ?_⟩
      dsimp only
      rw [hNextFrame.measure, hFrame.measure]
      exact retryFuel_decreases fuel hFuel
  · obtain ⟨fuel, source, tracked, hFrame, hTime, hCurrent, hReserved⟩ := hDone
    rw [← List.take_append_drop 7 advanceLoop]
    apply advance_completed_guard_spec env store frame fuel n expected.time source.root
      (if tracked then source.root else 0) expected.time source.root hFrame
    exact ⟨heap, hStore, fuel, source, tracked, hFrame, hTime, hCurrent, hReserved⟩

#print axioms advance_iteration_spec

end Project.EulerRiemann.Execution
