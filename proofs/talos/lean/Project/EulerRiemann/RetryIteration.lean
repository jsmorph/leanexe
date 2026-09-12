import Project.EulerRiemann.RetryResources

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

local macro "retry_iteration_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [retryGuardFrame, retryTrialFrame, retryAcceptedFrame, retryRejectedFrame,
        List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, Bool.false_eq_true, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

def retryIterationPost (initial : Store Unit) (initialHeap : Heap) (n : Nat)
    (time source need : UInt64) (grid : Array Traversal.Cell) (expected : Control.Attempt)
    (spare limit measure : Nat) : Assertion Unit
  | .Break 0 store frame =>
      retryInvariant initial initialHeap n time source need grid expected spare limit store frame ∧
        retryMeasure frame < measure
  | .Break 1 store frame =>
      ∃ heap, RetryStoreAt initial initialHeap store heap ∧
        RetryDone initial initialHeap n time source need expected spare limit store heap frame
  | _ => False

theorem retry_iteration_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (time : UInt64)
    (expected : Control.Attempt) (spare limit : Nat) (store : Store Unit) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hSuccess : expected.status = 0)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (hInv : retryInvariant initial initialHeap n time source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit store frame) :
    wp Project.EulerRiemann.«module» retryLoop
      (retryIterationPost initial initialHeap n time source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit (retryMeasure frame))
      store frame env := by
  obtain ⟨heap, hStore, hState⟩ := hInv
  rcases hState with hActive | hDone
  · obtain ⟨fuel, dt, hFrame, hSame, hReserved⟩ := hActive
    have hSourceSuccess : (Control.retry fuel.toNat n time dt grid).status = 0 := by
      rw [hSame]
      exact hSuccess
    have hFuel := retry_success_nonzero fuel n time dt grid hSourceSuccess
    have hFuelNat := retryFuel_unfold fuel hFuel
    have hValid : Time.validAdvance time dt = true := by
      cases hV : Time.validAdvance time dt with
      | false => simp [hFuelNat, Control.retry, hV] at hSourceSuccess
      | true => rfl
    have hCurrentOwner := hStore.held source grid hOwner
    have hCurrentCap : limit ≤ store.memoryCap Project.EulerRiemann.«module» 0 * 65536 := by
      rw [hStore.cap]
      exact hCap
    have hParams := hFrame.params
    have hLocals := hFrame.locals
    have hValues := hFrame.values
    rcases frame with ⟨params, locals, values⟩
    dsimp only at hParams hLocals hValues ⊢
    subst params
    subst values
    let frame : Locals := ⟨[.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 dt, .i64 source.root, .i64 source.root], locals, []⟩
    rw [retry_loop_parts, List.append_assoc]
    apply retry_active_guard_spec env store frame fuel n time dt source.root 0 0 hFrame hFuel
    apply retry_validity_spec env store frame fuel n time dt source.root 0 0 false hFrame
    simp only [hValid]
    dsimp only [frame]
    retry_iteration_peel
    rw [retry_branches_shape]
    refine retry_trial_spec env store heap (retryGuardFrame frame time dt true) fuel source grid
      n time dt spare limit (hFrame.guard true).params (hFrame.guard true).locals
      (hFrame.guard true).values hn hIndexed hStore.heapState hCurrentOwner hStore.pages
      hReserved hLimit hCurrentCap _ _ ?_
    intro ratio need result final hFinalHeap hFinalOwner hFinalPages hFinalCap hFinalReserved hCapacity hHeld
    have hPreserved := hStore.after_step hFinalHeap hFinalPages hFinalCap result.2 hHeld
    have hNewStore := hPreserved.1
    have hSeparated := hPreserved.2
    simp only [hFuelNat, Control.retry, hValid, ite_true] at hSame
    cases hAccepted : Traversal.accepted (Traversal.step n ratio grid) with
    | true =>
      have hTrialFrame := (hFrame.guard true).trial ratio result.2.root true
      have hDt : expected.dt = dt := by
        simpa only [ratio, hAccepted, ite_true] using (congrArg Control.Attempt.dt hSame).symm
      have hGrid : expected.grid = Traversal.step n ratio grid := by
        simpa only [ratio, hAccepted, ite_true] using (congrArg Control.Attempt.grid hSame).symm
      dsimp only [frame]
      retry_iteration_peel
      apply retry_accept_spec env final (retryGuardFrame frame time dt true) n fuel time dt
        source.root ratio result.2.root (hFrame.guard true).params (hFrame.guard true).locals
      dsimp only [frame]
      retry_iteration_peel
      have hDoneFrame := hTrialFrame.accept result.2.root
      simp only [retryAcceptedFrame, retryTrialFrame, retryGuardFrame, boolWord, reduceIte] at hDoneFrame
      change retryInvariant _ _ _ _ _ _ _ _ _ _ _ _ ∧ _
      refine ⟨⟨result.1, hNewStore, Or.inr ⟨fuel, dt, result.2, ?_, ?_,
        hFinalReserved, hCapacity, hSeparated⟩⟩, ?_⟩
      · simpa only [hDt] using hDoneFrame
      · simpa only [hGrid] using hFinalOwner
      · rw [hDoneFrame.measure, hFrame.measure]
        simp
    | false =>
      have hTrialFrame := (hFrame.guard true).trial ratio result.2.root false
      have hSource : source.root ≠ 0 := by
        intro hZero
        have hRoot := hOwner.buffer.rootBound
        simp [hZero] at hRoot
      have hNextSame : Control.retry (fuel - 1).toNat n time
          (IEEE64.mul 0x3FE0000000000000 dt) grid = expected := by
        simpa only [ratio, hAccepted, Bool.false_eq_true, ite_false] using hSame
      dsimp only [frame]
      retry_iteration_peel
      apply retry_reject_spec env final result.1 (retryGuardFrame frame time dt true) n fuel time dt
        source.root ratio result.2 (Traversal.step n ratio grid) (hFrame.guard true).params
        (hFrame.guard true).locals (hFrame.guard true).tracker hSource hFinalHeap hFinalOwner
      dsimp only [frame]
      retry_iteration_peel
      have hNextStore := hNewStore.released result.2 _ hFinalOwner hSeparated
      have hNextReserved := hFinalReserved.release result.2 hCapacity
      have hNextFrame := hTrialFrame.reject (result.1.frees + 1)
      simp only [retryRejectedFrame, retryTrialFrame, retryGuardFrame, boolWord,
        Bool.false_eq_true, reduceIte] at hNextFrame
      change retryInvariant _ _ _ _ _ _ _ _ _ _ _ _ ∧ _
      refine ⟨⟨result.1.release result.2, hNextStore,
        Or.inl ⟨fuel - 1, IEEE64.mul 0x3FE0000000000000 dt, hNextFrame, hNextSame, hNextReserved⟩⟩, ?_⟩
      rw [hNextFrame.measure, hFrame.measure]
      exact retryFuel_decreases fuel hFuel
  · obtain ⟨fuel, dt, result, hFrame, hResult, hReserved, hCapacity, hSeparated⟩ := hDone
    rw [← List.take_append_drop 7 retryLoop]
    apply retry_completed_guard_spec env store frame fuel n time dt source.root expected.dt
      result.root hFrame
    exact ⟨heap, hStore, fuel, dt, result, hFrame, hResult, hReserved, hCapacity, hSeparated⟩

#print axioms retry_iteration_spec

end Project.EulerRiemann.Execution
