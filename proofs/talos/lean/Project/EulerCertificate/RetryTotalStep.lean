import Project.EulerCertificate.RetryInvariant
import Project.EulerCertificate.AttemptExecution

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerCertificate.Control (Attempt)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

macro "certificate_retry_total_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [retryGuardFrame, retryTrialFrame, retryAcceptedFrame, retryRejectedFrame,
        vectorValues, boundsValues, Vectors.zero, Project.ProofKit.F64Interval.point,
        List.append_eq, List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, Bool.false_eq_true, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem retry_total_step_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (fuel trials time dt alpha ratio : UInt64)
    (expected : Attempt) (spare limit pageLimit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerCertificate.«module» 0 * 65536)
    (hStore : RetryStoreAt initial initialHeap store heap)
    (hPages : store.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hLimitPages : limit ≤ pageLimit * 65536)
    (hFrame : RetryFrameAt frame fuel n trials time dt alpha source.root 0 0 false)
    (hScratch : RetryScratch frame) (hRatio : frame.locals[27]? = some (.i64 ratio))
    (hSame : (match Control.attempt n trials.toNat dt ratio grid with
      | some trial => ({ status := 0, dt, grid := trial.grid, boundary := trial.boundary } : Attempt)
      | none => Control.retry (fuel - 1).toNat n trials.toNat time
          (IEEE64.mul 0x3FE0000000000000 dt) alpha grid) = expected)
    (hReserved : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hFuel : fuel ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      retryTotalInvariant initial initialHeap n trials time alpha source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit final resultFrame →
      retryMeasure resultFrame < retryMeasure frame → wp Project.EulerCertificate.«module» rest Q final resultFrame env) :
    wp Project.EulerCertificate.«module» (retryStepBody ++ rest) Q store frame env := by
  have hCurrentCap : limit ≤ store.memoryCap Project.EulerCertificate.«module» 0 * 65536 := by
    change limit ≤ store.memoryCap Project.EulerRiemann.«module» 0 * 65536
    rw [hStore.cap]
    exact hCap
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  rcases frame with ⟨params, locals, values⟩
  dsimp only at hParams hLocals hValues ⊢
  subst params
  subst values
  let frame : Locals := ⟨[.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
    .i64 dt, .i64 alpha, .i64 source.root, .i64 source.root], locals, []⟩
  rw [retry_trial_branches_shape]
  unfold retryStepBody retryTrial retryLoop func179
  dsimp only
  certificate_retry_total_peel
  refine wp_call_tw (attempt_pages_exact env store heap source grid n trials dt ratio spare limit pageLimit
    hn hIndexed hStore.heapState (hStore.held source grid hOwner) hPages hPageLimit
    hReserved hLimit hCurrentCap hLimitPages) ?_
  intro final values hResult
  obtain ⟨finalHeap, hResultStore, hFinalPages, hResult⟩ := hResult
  have hNewStore : RetryStoreAt initial initialHeap final finalHeap :=
    ⟨hResultStore.heapState, hResultStore.pages, hResultStore.cap.trans hStore.cap,
      fun saved savedGrid hSaved => hResultStore.held saved savedGrid (hStore.held saved savedGrid hSaved)⟩
  cases hAttempt : Control.attempt n trials.toNat dt ratio grid with
  | none =>
    simp only [hAttempt] at hResult hSame
    obtain ⟨rfl, hFinalReserved⟩ := hResult
    have hTrial := hFrame.trial ratio 0 0 Vectors.zero
    have hTrialScratch := hScratch.trial n trials dt ratio source.root 0 0 Vectors.zero
    have hNextFrame := hTrial.reject
    have hNextScratch := hTrialScratch.reject fuel n trials time dt alpha source.root
    simp only [retryRejectedFrame, retryTrialFrame, Vectors.zero] at hNextFrame hNextScratch
    have hSource : source.root ≠ 0 := by
      intro hZero
      have hRoot := hOwner.buffer.rootBound
      simp [hZero] at hRoot
    certificate_retry_total_peel
    change wp _ retryRejectBody _ final
      (retryTrialFrame frame n trials dt ratio source.root 0 0 Vectors.zero) env
    apply retry_reject_spec env final _ fuel n trials time dt alpha source.root 0 0 false hTrial hSource
    certificate_retry_total_peel
    apply hNext
    · exact ⟨finalHeap, hNewStore, hFinalPages,
        Or.inl ⟨⟨fuel - 1, IEEE64.mul 0x3FE0000000000000 dt, hNextFrame,
          hSame, hFinalReserved⟩, hNextScratch⟩⟩
    · rw [hNextFrame.measure, hFrame.measure]
      exact retryFuel_decreases fuel hFuel
  | some trial =>
    simp only [hAttempt] at hResult hSame
    obtain ⟨result, rfl, hResultOwner, hFinalReserved, hCapacity, hSeparated⟩ := hResult
    have hTrial := hFrame.trial ratio 1 result.root trial.boundary
    have hDoneFrame := hTrial.accept result.root trial.boundary
    simp only [retryAcceptedFrame, retryTrialFrame] at hDoneFrame
    have hExpected : expected = ⟨0, dt, trial.grid, trial.boundary⟩ := hSame.symm
    clear hSame
    certificate_retry_total_peel
    change wp _ retryAcceptBody _ final
      (retryTrialFrame frame n trials dt ratio source.root 1 result.root trial.boundary) env
    apply retry_accept_spec env final frame n fuel trials time dt alpha source.root ratio result.root
      trial.boundary rfl hLocals
    certificate_retry_total_peel
    apply hNext
    · refine ⟨finalHeap, hNewStore, hFinalPages, Or.inr ⟨result, ?_, ?_,
        hFinalReserved, fun _ => hCapacity, ?_⟩⟩
      · simpa only [hExpected] using hDoneFrame
      · simpa only [hExpected] using hResultOwner
      · intro saved savedGrid hSaved
        exact hSeparated saved savedGrid (hStore.held saved savedGrid hSaved)
    · rw [hDoneFrame.measure, hFrame.measure]
      simp

#print axioms retry_total_step_spec
end Project.EulerCertificate.Execution
