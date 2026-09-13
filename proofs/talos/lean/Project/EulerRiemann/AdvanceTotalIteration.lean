import Project.EulerRiemann.AdvanceTotalWork
import Project.ProofKit.BlockLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

def advanceTotalIterationPost (initial : Store Unit) (initialHeap : Heap) (n : Nat) (startTime : UInt64)
    (expected : Control.Result) (spare limit pageLimit measure : Nat) : Assertion Unit :=
  BlockLoop.stepPost
    (advanceTotalInvariant initial initialHeap n startTime expected spare limit pageLimit)
    (fun store frame => ∃ heap, RetryStoreAt initial initialHeap store heap ∧ store.mem.pages ≤ pageLimit ∧
      AdvanceTotalDone initial initialHeap n startTime expected spare limit store heap frame)
    (fun _ frame => advanceMeasure frame) measure

theorem advance_total_iteration_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n : Nat) (startTime : UInt64) (expected : Control.Result) (spare limit pageLimit : Nat)
    (store : Store Unit) (frame : Locals) (hn : 2 ≤ n ∧ n ≤ 800)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPageLimit : pageLimit ≤ 65536) (hLimitPages : limit ≤ pageLimit * 65536)
    (hInv : advanceTotalInvariant initial initialHeap n startTime expected spare limit pageLimit store frame) :
    wp module advanceLoop
      (advanceTotalIterationPost initial initialHeap n startTime expected spare limit pageLimit (advanceMeasure frame))
      store frame env := by
  obtain ⟨heap, hStore, hPages, hActive | hDone⟩ := hInv
  · obtain ⟨fuel, time, source, grid, tracked, hFrame, hSame, hEnough, hCurrent, hReserve⟩ := hActive
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
    rw [advance_loop_parts, List.append_assoc]
    apply advance_active_guard_spec env store frame fuel n time source.root
      (if tracked then source.root else 0) 0 0 hFrame hFuel
    apply advance_time_spec env store frame hFrame.locals (by rw [hFrame.params]; rfl) hFrame.values
    by_cases hTime : time = Time.endTime
    · subst time
      have hExpected : expected = { status := 0, time := Time.endTime, grid } := by
        simpa [hFuelNat, Control.advance] using hSame.symm
      dsimp only [frame]
      advance_total_peel
      apply advance_finish_spec env store (advanceTimeFrame frame) fuel n Time.endTime source.root
        (if tracked then source.root else 0) 0 0 false hFrame.time
      dsimp only [frame]
      advance_total_peel
      have hFinished := hFrame.time.finish.returned
      simp only [advanceFinishedFrame, advanceTimeFrame] at hFinished
      have hReserved : heap.Reserved (gridCapacity n) (spare + 1) limit := by
        apply hReserve.mono
        cases tracked <;> simp
      change advanceTotalInvariant _ _ _ _ _ _ _ _ _ _ ∧ _
      refine ⟨⟨heap, hStore, hPages, Or.inr ⟨source, tracked, ?_, ?_, hReserved⟩⟩, ?_⟩
      · simpa only [hExpected] using hFinished
      · simpa only [hExpected] using hCurrent
      · dsimp only
        rw [hFinished.measure, hFrame.measure]
        simp
    · dsimp only [frame]
      advance_total_peel
      refine advance_total_work_spec env initial initialHeap n startTime expected spare limit pageLimit
        store heap frame fuel time source grid tracked hn hLimit hCap hStore hPages hPageLimit hLimitPages hFrame hSame hEnough
        hCurrent hReserve hTime _ [] ?_
      intro final resultFrame hFinal hDecrease
      have hEmpty : ({ resultFrame with values := [] } : Locals) = resultFrame :=
        Frame.ext _ _ rfl rfl hFinal.values.symm
      simpa [wp_simp, advanceTotalIterationPost, BlockLoop.stepPost, hEmpty, frame] using
        And.intro hFinal hDecrease
  · obtain ⟨source, tracked, hFrame, hCurrent, hReserved⟩ := hDone
    rw [← List.take_append_drop 7 advanceLoop]
    apply advance_returned_guard_spec env store frame expected.status expected.time source.root hFrame
    exact ⟨heap, hStore, hPages, source, tracked, hFrame, hCurrent, hReserved⟩

#print axioms advance_total_iteration_spec

end Project.EulerRiemann.Execution
