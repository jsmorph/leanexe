import Project.EulerRiemann.RetryTotalInvariant

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

macro "retry_total_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [retryGuardFrame, retryTrialFrame, retryAcceptedFrame, retryRejectedFrame,
        List.append_eq, List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, Bool.false_eq_true, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem retry_total_valid_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (fuel time dt : UInt64)
    (expected : Control.Attempt) (spare limit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hStore : RetryStoreAt initial initialHeap store heap)
    (hFrame : RetryFrameAt frame fuel n time dt source.root 0 0 false)
    (hScratch : RetryScratch frame) (hSame : Control.retry fuel.toNat n time dt grid = expected)
    (hReserved : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hFuel : fuel ≠ 0) (hValid : Time.validAdvance time dt = true)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      retryTotalInvariant initial initialHeap n time source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit final resultFrame →
      retryMeasure resultFrame < retryMeasure frame → wp module rest Q final resultFrame env) :
    wp module (retryTrial ++ rest) Q store (retryGuardFrame frame time dt true) env := by
  have hFuelNat := retryFuel_unfold fuel hFuel
  have hCurrentOwner := hStore.held source grid hOwner
  have hCurrentCap : limit ≤ store.memoryCap module 0 * 65536 := by
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
    have hStatus : expected.status = 0 := by
      simpa only [ratio, hAccepted, ite_true] using (congrArg Control.Attempt.status hSame).symm
    have hDt : expected.dt = dt := by
      simpa only [ratio, hAccepted, ite_true] using (congrArg Control.Attempt.dt hSame).symm
    have hGrid : expected.grid = Traversal.step n ratio grid := by
      simpa only [ratio, hAccepted, ite_true] using (congrArg Control.Attempt.grid hSame).symm
    dsimp only [frame]
    retry_total_peel
    apply retry_accept_spec env final (retryGuardFrame frame time dt true) n fuel time dt
      source.root ratio result.2.root (hFrame.guard true).params (hFrame.guard true).locals
    dsimp only [frame]
    retry_total_peel
    have hDoneFrame := (hTrialFrame.accept result.2.root).returned
    simp only [retryAcceptedFrame, retryTrialFrame, retryGuardFrame, boolWord, reduceIte] at hDoneFrame
    apply hNext
    · refine ⟨result.1, hNewStore, Or.inr ⟨result.2, ?_, ?_,
        hFinalReserved, fun _ => hCapacity, hSeparated⟩⟩
      · simpa only [hStatus, hDt] using hDoneFrame
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
    retry_total_peel
    apply retry_reject_spec env final result.1 (retryGuardFrame frame time dt true) n fuel time dt
      source.root ratio result.2 (Traversal.step n ratio grid) (hFrame.guard true).params
      (hFrame.guard true).locals (hFrame.guard true).tracker hSource hFinalHeap hFinalOwner
    dsimp only [frame]
    retry_total_peel
    have hNextStore := hNewStore.released result.2 _ hFinalOwner hSeparated
    have hNextReserved := hFinalReserved.release result.2 hCapacity
    have hNextFrame := hTrialFrame.reject (result.1.frees + 1)
    have hNextScratch := ((hScratch.guard time dt true).trial n ratio source.root result.2.root false).reject
      fuel n time dt source.root (result.1.frees + 1)
    simp only [retryRejectedFrame, retryTrialFrame, retryGuardFrame, boolWord,
      Bool.false_eq_true, reduceIte] at hNextFrame hNextScratch
    apply hNext
    · exact ⟨result.1.release result.2, hNextStore,
        Or.inl ⟨⟨fuel - 1, IEEE64.mul 0x3FE0000000000000 dt, hNextFrame, hNextSame, hNextReserved⟩,
          hNextScratch⟩⟩
    · rw [hNextFrame.measure, hFrame.measure]
      exact retryFuel_decreases fuel hFuel

#print axioms retry_total_valid_spec

end Project.EulerRiemann.Execution
