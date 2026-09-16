import Project.EulerCertificate.RetryInvariant
import Project.EulerCertificate.RetryZero

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity FixedArrayFold
open Project.EulerRiemann.Execution
open Project.EulerRiemann
open Project.EulerCertificate.Control (Attempt)

theorem retry_total_invalid_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n : Nat) (fuel trials time dt alpha source : UInt64) (grid : Array Project.EulerRiemann.Traversal.Cell)
    (expected : Attempt) (spare limit pageLimit : Nat) (store : Store Unit) (heap : Heap) (frame : Locals)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hStore : RetryStoreAt initial initialHeap store heap)
    (hPages : store.mem.pages ≤ pageLimit) (hLimitPages : limit ≤ pageLimit * 65536)
    (hFrame : RetryFrameAt frame fuel n trials time dt alpha source 0 0 false)
    (hScratch : RetryScratch frame) (hSame : Control.retry fuel.toNat n trials.toNat time dt alpha grid = expected)
    (hReserved : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hFuel : fuel ≠ 0) (hValid : Time.validAdvance time dt = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      retryTotalInvariant initial initialHeap n trials time alpha source
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit final resultFrame →
      retryMeasure resultFrame < retryMeasure frame → wp module rest Q final resultFrame env) :
    wp module (retryFailureProgram 3 ++ retryZeroBoundary 88 ++ [.constI64 1, .localSet 25] ++ rest) Q
      store (retryGuardFrame frame time dt false) env := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  have hNeed : (8 : UInt64) ≤ need := by
    rw [UInt64.le_iff_toNat_le]
    exact normalizedCapacity_toNat_ge_eight ..
  have hBound : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 ≤ limit :=
    hReserved.bump_small_bound (by omega) hNeed
  have hCurrentCap : limit ≤ store.memoryCap module 0 * 65536 := by
    change limit ≤ store.memoryCap Project.EulerRiemann.«module» 0 * 65536
    rw [hStore.cap]
    exact hCap
  have hBump : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + 8 ≤ 4294967296 ∧ bumpPages heap.top 8 ≤ store.memoryCap module 0 := by
    intro hNone
    have hBytes := hBound hNone
    constructor
    · omega
    · simp only [bumpPages, show (8 : UInt64).toNat = 8 from rfl]
      omega
  have hResource := hStore.empty need spare limit hReserved hNeed hLimit
  have hFinalPages := heap.emptyStore_pages_bound store need spare limit pageLimit
    hPages hReserved hNeed hLimitPages
  have hFuelNat := retryFuel_unfold fuel hFuel
  have hExpected : expected = { status := 3, dt, grid := #[], boundary := Vectors.zero } := by
    simpa only [hFuelNat, Control.retry, hValid, Bool.false_eq_true, ite_false] using hSame.symm
  let before := retryGuardFrame frame time dt false
  let params := before.params
  let saved := before.locals.take 115
  have hBefore := hFrame.guard false
  have hParams : params.length = 8 := by simp [params, before, hFrame.params, retryGuardFrame]
  have hSaved : saved.length = 115 := by
    simp [saved, before, retryGuardFrame, hFrame.locals]
  have hDt : params[4]? = some (.i64 dt) := by
    simp [params, before, retryGuardFrame, hFrame.params]
  have hFirst : ∃ value : UInt64, params[0]? = some (.i64 value) :=
    ⟨fuel, by simp [params, before, retryGuardFrame, hFrame.params]⟩
  have hInput := (hScratch.guard time dt false).frame_eq hBefore.values
  change before = FixedArraySearch.frame params saved [] 0 0 0 0 0 0 at hInput
  change wp module _ _ store before env
  rw [hInput]
  simp only [List.append_assoc]
  apply retry_failure_program_spec env store heap params saved hParams hSaved
    3 dt 0 0 0 0 0 0 hDt hStore.heapState hBump hStore.pages
  intro previous current capacity next
  apply retry_zero_spec env (heap.emptyStore store) _ 88 (Or.inl rfl)
    (by simp [retryFailureFrame, FixedArrayResult.finishFrame, resultFrame,
      FixedArraySearch.frame, hParams])
    (by simp [retryFailureFrame, FixedArrayResult.finishFrame, resultFrame,
      FixedArraySearch.frame, retryFailureSaved, hSaved]) rfl
  have hReturned := retry_failure_returned params saved hParams hSaved hFirst
    3 dt previous current capacity next (allocatedRoot heap.top 8 heap.nodes) 88 (Or.inl rfl)
  simp only [retryZeroFrame, resultFrame, retryFailureFrame, FixedArrayResult.finishFrame,
    FixedArraySearch.frame, retryFailureSaved, hParams, Nat.reduceSub, List.append_nil] at hReturned
  wp_run [retryZeroFrame, retryFailureFrame, FixedArrayResult.finishFrame, resultFrame,
    FixedArraySearch.frame, retryFailureSaved, hParams, hSaved,
    List.cons_append, List.nil_append, List.length_append, List.length_set, List.getElem?_set,
    reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  apply hNext
  · refine ⟨heap.allocate 8, hResource.1, hFinalPages,
      Or.inr ⟨allocatedNode heap.top 8 heap.nodes, ?_, ?_, hResource.2.2.1, ?_, hResource.2.2.2⟩⟩
    · simpa only [hExpected, allocatedNode] using hReturned
    · simpa only [hExpected] using hResource.2.1
    · simp [hExpected]
  · rw [hReturned.measure, hFrame.measure]
    simp

#print axioms retry_total_invalid_spec

end Project.EulerCertificate.Execution
