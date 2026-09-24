import Project.EulerRiemann.FrozenAdvanceTotalInvariant
import Project.EulerRiemann.FrozenAdvanceTotalTrial

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

macro "advance_total_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [advanceTimeFrame, advanceScanFrame, advanceTrialFrame,
        advanceFinishedFrame, advanceReturnedFrame, advanceReturnTail, advanceContinuedFrame,
        List.append_eq, List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, Bool.false_eq_true, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem advance_total_work_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n : Nat) (startTime : UInt64) (expected : Control.Result) (spare limit pageLimit : Nat)
    (store : Store Unit) (heap : Heap) (frame : Locals) (fuel time : UInt64)
    (source : FreeNode) (grid : Array Traversal.Cell) (tracked : Bool)
    (hn : 2 ≤ n ∧ n ≤ 800) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hStore : RetryStoreAt initial initialHeap store heap)
    (hPages : store.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hLimitPages : limit ≤ pageLimit * 65536)
    (hFrame : AdvanceFrameAt frame fuel n time source.root (if tracked then source.root else 0) 0 0 false)
    (hSame : Control.advance fuel.toNat n time grid = expected)
    (hEnough : Time.endTime.toNat - time.toNat < fuel.toNat)
    (hCurrent : AdvanceCurrent initial initialHeap n startTime time store heap source grid tracked)
    (hReserve : heap.Reserved (gridCapacity n) (spare + if tracked then 2 else 3) limit)
    (hTime : time ≠ Time.endTime) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      advanceTotalInvariant initial initialHeap n startTime expected spare limit pageLimit final resultFrame →
      advanceMeasure resultFrame < advanceMeasure frame → wp module rest Q final resultFrame env) :
    wp module (advanceWorkBody ++ rest) Q store (advanceTimeFrame frame) env := by
  have hFuel : fuel ≠ 0 := by intro h; simp [h] at hEnough
  have hFuelNat := retryFuel_unfold fuel hFuel
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  rcases frame with ⟨params, locals, values⟩
  dsimp only at hParams hLocals hValues ⊢
  subst params
  subst values
  let frame : Locals := ⟨[.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
    .i64 source.root, .i64 source.root], locals, []⟩
  rw [advance_work_shape, List.append_assoc]
  refine advance_scan_spec env store (advanceTimeFrame frame) n fuel time source.root grid
    hFrame.time.params hFrame.time.locals hFrame.time.values hCurrent.owner.buffer.values _ _ ?_
  by_cases hScan : (Traversal.scan grid).status = 0
  · have hScanned := hFrame.time.scan { status := 0, alpha := (Traversal.scan grid).alpha }
    have hCurrentCap : limit ≤ store.memoryCap module 0 * 65536 := by rw [hStore.cap]; exact hCap
    let callSpare := spare + if tracked then 0 else 1
    have hTrialReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7)
        (callSpare + 2) limit := by
      cases tracked <;> simpa [gridCapacity, hCurrent.indexed.1, callSpare, Nat.add_assoc] using hReserve
    dsimp only [frame]
    advance_total_peel
    rw [advance_trial_shape]
    refine advance_total_trial_spec env store heap (advanceScanFrame (advanceTimeFrame frame) source.root
      { status := 0, alpha := (Traversal.scan grid).alpha })
      fuel source grid n time (Traversal.scan grid).alpha callSpare limit pageLimit hScanned.params hScanned.locals
      hScanned.values (by simp [advanceScanFrame, advanceTimeFrame, frame, hLocals])
      hn hCurrent.indexed hStore.heapState hCurrent.owner hPages hPageLimit hTrialReserve hLimit hCurrentCap hLimitPages _ _ ?_
    intro dt trial final finalHeap result hTrialStore hTrialPages hTrialOwner hTrialReserved hTrialCapacity hSeparated
    have hTrialFrame := hScanned.trial (Traversal.scan grid).alpha dt trial.dt result.root trial.status
    by_cases hTrialSuccess : trial.status = 0
    · have hNextSame : Control.advance (fuel - 1).toNat n (IEEE64.add time trial.dt) trial.grid = expected := by
        simpa [hFuelNat, Control.advance, hTime, hScan, dt, trial, hTrialSuccess] using hSame
      have hTrialValid := (Control.retry_success (dt.toNat + 1) n time dt grid hTrialSuccess).1
      have hDecrease := Time.remaining_decreases time trial.dt hTrialValid
      have hNextEnough : Time.endTime.toNat - (IEEE64.add time trial.dt).toNat < (fuel - 1).toNat := by omega
      have hNextIndexed := Control.retry_indexed (dt.toNat + 1) n time dt grid hCurrent.indexed hTrialSuccess
      have hNextCapacity : gridCapacity n ≤ result.capacity := by
        simpa only [gridCapacity, hCurrent.indexed.1] using hTrialCapacity hTrialSuccess
      have hNextReserved : finalHeap.Reserved (gridCapacity n) (spare + if tracked then 1 else 2) limit := by
        cases tracked <;> simpa [gridCapacity, hCurrent.indexed.1, callSpare, Nat.add_assoc] using hTrialReserved
      have hReplacement := hCurrent.replace hStore hTrialStore result trial.grid (IEEE64.add time trial.dt)
        spare limit hNextIndexed hTrialOwner hNextCapacity hSeparated hNextReserved
      have hReplacementPages :
          (if tracked then finalHeap.releaseStore final source else final).mem.pages ≤ pageLimit := by
        cases tracked <;> simpa [Heap.releaseStore, releasedStore_pages] using hTrialPages
      have hSource : source.root ≠ 0 := by
        intro hZero
        have hRoot := hCurrent.owner.buffer.rootBound
        simp [hZero] at hRoot
      have hDifferent := freeNode_roots_ne source result (hSeparated source grid hCurrent.owner)
      dsimp only [frame]
      advance_total_peel
      apply advance_continue_spec env final finalHeap
        (advanceScanFrame (advanceTimeFrame frame) source.root
          { status := 0, alpha := (Traversal.scan grid).alpha }) fuel source grid
        n time (Traversal.scan grid).alpha dt trial.dt result.root tracked
        hScanned.params hScanned.locals hScanned.tracker hSource hDifferent hTrialStore.heapState
        (hTrialStore.held source grid hCurrent.owner)
      dsimp only [frame]
      advance_total_peel
      have hNextFrame := hTrialFrame.continued (IEEE64.add time trial.dt) result.root
      simp only [advanceContinuedFrame, advanceTrialFrame, advanceScanFrame, advanceTimeFrame,
        hTrialSuccess] at hNextFrame
      apply hNext
      · exact ⟨_, hReplacement.1, hReplacementPages, Or.inl ⟨fuel - 1, IEEE64.add time trial.dt, result, trial.grid, true,
          hNextFrame, hNextSame, hNextEnough, hReplacement.2.1, hReplacement.2.2⟩⟩
      · rw [hNextFrame.measure, hFrame.measure]
        exact retryFuel_decreases fuel hFuel
    · have hExpected : expected = { status := trial.status, time, grid } := by
        simpa [hFuelNat, Control.advance, hTime, hScan, dt, trial, hTrialSuccess] using hSame.symm
      have hReturned := hTrialFrame.return_status trial.status
      have hFinalCurrent := hCurrent.preserved hTrialStore
      have hReserved : finalHeap.Reserved (gridCapacity n) (spare + 1) limit := by
        have hBound := hTrialReserved.mono (show spare + 1 ≤ callSpare + 1 by
          dsimp only [callSpare]
          omega)
        simpa only [gridCapacity, hCurrent.indexed.1] using hBound
      dsimp only [frame]
      advance_total_peel
      rw [advance_trial_failure_shape]
      advance_total_peel
      simp only [advanceReturnedFrame, advanceTrialFrame, advanceScanFrame, advanceTimeFrame] at hReturned
      apply hNext
      · refine ⟨finalHeap, hStore.trans hTrialStore, hTrialPages, Or.inr ⟨source, tracked, ?_, ?_, ?_⟩⟩
        · simpa only [hExpected] using hReturned
        · simpa only [hExpected] using hFinalCurrent
        · simpa only [gridCapacity, hCurrent.indexed.1] using hReserved
      · rw [hReturned.measure, hFrame.measure]
        simp
  · have hExpected : expected = { status := 2, time, grid } := by
      simpa [hFuelNat, Control.advance, hTime, hScan] using hSame.symm
    have hScanned := hFrame.time.scan (Traversal.scan grid)
    have hReturned := hScanned.return_status 2
    have hReserved : heap.Reserved (gridCapacity n) (spare + 1) limit := by
      apply hReserve.mono
      cases tracked <;> simp
    dsimp only [frame]
    advance_total_peel
    rw [advance_scan_failure_shape]
    advance_total_peel
    simp only [advanceReturnedFrame, advanceScanFrame, advanceTimeFrame] at hReturned
    apply hNext
    · refine ⟨heap, hStore, hPages, Or.inr ⟨source, tracked, ?_, ?_, hReserved⟩⟩
      · simpa only [hExpected] using hReturned
      · simpa only [hExpected] using hCurrent
    · rw [hReturned.measure, hFrame.measure]
      simp

#print axioms advance_total_work_spec

end Project.EulerRiemann.Frozen.Execution
