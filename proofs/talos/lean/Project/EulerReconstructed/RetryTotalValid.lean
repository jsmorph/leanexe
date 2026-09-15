import Project.EulerReconstructed.RetryTotalStep

namespace Project.EulerReconstructed.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerRiemann.Control (Attempt)

theorem retry_ratio_parts : retryTrial = retryTrial.take 16 ++
    [.localGet 22, .constI64 0, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 0, .eqI64, .eqz, .iff 0 0 retryStepBody retryCflRejectBody] := rfl

macro "reconstructed_retry_ratio_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [retryGuardFrame, retryRatioFrame, List.append_eq, List.cons_append,
        List.nil_append, List.length_set, List.getElem?_set, List.getElem?_cons_zero,
        List.getElem?_cons_succ, boolWord, Bool.false_eq_true, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem retry_total_valid_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat)
    (fuel trials time dt alpha : UInt64) (expected : Attempt) (spare limit pageLimit : Nat)
    (store : Store Unit) (heap : Heap) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hStore : RetryStoreAt initial initialHeap store heap)
    (hPages : store.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hLimitPages : limit ≤ pageLimit * 65536)
    (hFrame : RetryFrameAt frame fuel n trials time dt alpha source.root 0 0 false)
    (hScratch : RetryScratch frame)
    (hSame : Control.retry fuel.toNat n trials.toNat time dt alpha grid = expected)
    (hReserved : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hFuel : fuel ≠ 0) (hValid : Time.validAdvance time dt = true)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      retryTotalInvariant initial initialHeap n trials time alpha source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit final resultFrame →
      retryMeasure resultFrame < retryMeasure frame → wp module rest Q final resultFrame env) :
    wp module (retryTrial ++ rest) Q store (retryGuardFrame frame time dt true) env := by
  have hFuelNat := retryFuel_unfold fuel hFuel
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  rcases frame with ⟨params, locals, values⟩
  dsimp only at hParams hLocals hValues ⊢
  subst params
  subst values
  let frame : Locals := ⟨[.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
    .i64 dt, .i64 alpha, .i64 source.root, .i64 source.root], locals, []⟩
  let checked := OutwardCfl.gridRatioChecked n dt alpha
  let ratioFrame := retryRatioFrame (retryGuardFrame frame time dt true) n dt alpha checked
  have hRatioFrame := (hFrame.guard true).ratio checked
  have hRatioMeasure : retryMeasure ratioFrame = fuel.toNat + 1 := by
    simpa using hRatioFrame.measure
  have hRatioScratch := (hScratch.guard time dt true).ratio n dt alpha checked
  have hRatio : ratioFrame.locals[15]? = some (.i64 checked.value) := by
    simp [ratioFrame, retryRatioFrame, retryGuardFrame, frame, hLocals]
  rw [retry_ratio_parts, List.append_assoc]
  apply retry_ratio_spec env store (retryGuardFrame frame time dt true) fuel n trials time dt alpha
    source.root 0 0 false hn.2 (hFrame.guard true)
  by_cases hChecked : (OutwardCfl.gridRatioChecked n dt alpha).status = 0
  · have hSameStep : (if Project.EulerRiemann.Traversal.accepted
        (Traversal.step n trials.toNat checked.value grid)
        then ({ status := 0, dt, grid := Traversal.step n trials.toNat checked.value grid } : Attempt)
        else Control.retry (fuel - 1).toNat n trials.toNat time
          (IEEE64.mul 0x3FE0000000000000 dt) alpha grid) = expected := by
      simpa only [hFuelNat, Control.retry, hValid, ite_true, checked,
        beq_iff_eq, hChecked] using hSame
    dsimp only [frame]
    reconstructed_retry_ratio_peel
    convert retry_total_step_spec env initial initialHeap source grid n fuel trials time dt alpha
      checked.value expected spare limit pageLimit store heap ratioFrame hn hIndexed hOwner
      hLimit hCap hStore hPages hPageLimit hLimitPages hRatioFrame hRatioScratch hRatio
      hSameStep hReserved hFuel _ [] ?_ using 1
    · simp only [List.append_nil]
    · simp only [ratioFrame, retryRatioFrame, retryGuardFrame, frame, checked, hChecked,
        boolWord, reduceIte]
    · intro final resultFrame hFinal hDecrease
      have hEmpty : ({ resultFrame with values := [] } : Locals) = resultFrame :=
        Project.ProofKit.Frame.ext _ _ rfl rfl hFinal.values.symm
      simp only [wp_simp, hEmpty]
      apply hNext final resultFrame hFinal
      simpa only [hRatioMeasure, hFrame.measure, Bool.false_eq_true, ite_false] using hDecrease
  · have hNextSame : Control.retry (fuel - 1).toNat n trials.toNat time
        (IEEE64.mul 0x3FE0000000000000 dt) alpha grid = expected := by
      simpa only [hFuelNat, Control.retry, hValid, ite_true, checked,
        beq_iff_eq, hChecked, ite_false] using hSame
    have hSource : source.root ≠ 0 := by
      intro hZero
      have hRoot := hOwner.buffer.rootBound
      simp [hZero] at hRoot
    dsimp only [frame]
    reconstructed_retry_ratio_peel
    apply retry_cfl_reject_spec env store ratioFrame fuel n trials time dt alpha source.root
      0 0 false hRatioFrame hSource
    have hNextFrame := hRatioFrame.rejectCfl
    have hNextScratch := hRatioScratch.rejectCfl fuel n trials time dt alpha source.root
    simp only [wp_simp, retryCflRejectedFrame_empty]
    apply hNext
    · exact ⟨heap, hStore, hPages, Or.inl ⟨⟨fuel - 1, IEEE64.mul 0x3FE0000000000000 dt,
        hNextFrame, hNextSame, hReserved⟩, hNextScratch⟩⟩
    · rw [hNextFrame.measure, hFrame.measure]
      exact retryFuel_decreases fuel hFuel

#print axioms retry_ratio_parts
#print axioms retry_total_valid_spec
end Project.EulerReconstructed.Execution
