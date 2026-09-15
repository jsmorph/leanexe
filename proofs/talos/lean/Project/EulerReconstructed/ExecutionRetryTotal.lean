import Project.EulerReconstructed.RetryTotalLoop

namespace Project.EulerReconstructed.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity FixedArrayFold
open Project.EulerRiemann.Execution

theorem retry_pages_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (fuel trials time dt alpha : UInt64)
    (spare limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536) :
    let expected := Control.retry fuel.toNat n trials.toNat time dt alpha grid
    TerminatesWith env module 125 initial
      [.i64 source.root, .i64 source.root, .i64 alpha, .i64 dt, .i64 time,
        .i64 trials, .i64 (UInt64.ofNat n), .i64 fuel]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root, .i64 expected.dt, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧ final.mem.pages ≤ pageLimit ∧ finalHeap.Owns final result expected.grid ∧
        finalHeap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit ∧
        (expected.status = 0 → normalizedCapacity (UInt64.ofNat grid.size) 7 ≤ result.capacity) ∧
        ∀ (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region) := by
  let expected := Control.retry fuel.toNat n trials.toNat time dt alpha grid
  let entry := func125Def.toLocals [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
    .i64 dt, .i64 alpha, .i64 source.root, .i64 source.root]
  have hStart : RetryFrameAt entry fuel n trials time dt alpha source.root 0 0 false := by
    constructor <;> rfl
  have hScratch : RetryScratch entry := rfl
  have hInv : retryTotalInvariant initial heap n trials time alpha source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit initial entry :=
    ⟨heap, ⟨hHeap, hPages.trans hPageLimit, rfl, fun _ _ h => h⟩, hPages, Or.inl ⟨⟨fuel, dt, hStart, rfl, hReserve⟩, hScratch⟩⟩
  refine TerminatesWith.of_wp_entry_for (f := func125Def) rfl ?_ (by decide)
  change wp module func125 _ initial entry env
  rw [retry_loop_shape, List.append_assoc]
  have hEntryShape : func125.take 4 = [.constI64 0, .localSet 8, .constI64 0, .localSet 13] := rfl
  rw [hEntryShape]
  wp_run [entry, func125Def, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp _ ([.block 0 0 [.loop 0 0 retryLoop]] ++ func125.drop 5) _ initial entry env
  apply retry_total_loop_spec env initial heap source grid n trials time alpha expected spare limit pageLimit initial entry
    hn hIndexed hOwner hLimit hCap hPageLimit hLimitPages hInv
  intro final finalHeap resultFrame hStore hFinalPages hStopped
  rcases hStopped with hDone | ⟨lastDt, hFrame, hSame, hReserved, hLastScratch⟩
  · obtain ⟨result, hFrame, hResult, hReserved, hCapacity, hSeparated⟩ := hDone
    have hParams := hFrame.params
    have hLocals := hFrame.locals
    have hValues := hFrame.values
    have hFinished := hFrame.done
    have hStatus := hFrame.status
    have hDt := hFrame.outputDt
    have hOwnerRead := hFrame.outputOwner
    have hPointerRead := hFrame.outputPointer
    obtain ⟨hFinishedBound, hFinishedRead⟩ := List.getElem_of_getElem? hFrame.done
    obtain ⟨hStatusBound, hStatusRead⟩ := List.getElem_of_getElem? hFrame.status
    obtain ⟨hDtBound, hDtRead⟩ := List.getElem_of_getElem? hFrame.outputDt
    obtain ⟨hOwnerBound, hOwnerValue⟩ := List.getElem_of_getElem? hFrame.outputOwner
    obtain ⟨hPointerBound, hPointerValue⟩ := List.getElem_of_getElem? hFrame.outputPointer
    rw [retry_exhausted_shape]
    reconstructed_retry_guard_peel
    exact ⟨finalHeap, result, ⟨rfl, rfl, rfl⟩, hStore, hResult, hReserved, hCapacity, hSeparated⟩
  · let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    have hNeed : (8 : UInt64) ≤ need := by
      rw [UInt64.le_iff_toNat_le]
      exact normalizedCapacity_toNat_ge_eight ..
    have hBound : takeFirstFitFrom 0 8 finalHeap.nodes = none →
        finalHeap.top.toNat + 48 + 8 ≤ limit := hReserved.bump_small_bound (by omega) hNeed
    have hCurrentCap : limit ≤ final.memoryCap module 0 * 65536 := by
      change limit ≤ final.memoryCap Project.EulerRiemann.«module» 0 * 65536
      rw [hStore.cap]
      exact hCap
    have hBump : takeFirstFitFrom 0 8 finalHeap.nodes = none →
        finalHeap.top.toNat + 48 + 8 ≤ 4294967296 ∧
        bumpPages finalHeap.top 8 ≤ final.memoryCap module 0 := by
      intro hNone
      have hBytes := hBound hNone
      constructor
      · omega
      · simp only [bumpPages, show (8 : UInt64).toNat = 8 from rfl]
        omega
    have hResource := hStore.empty need spare limit hReserved hNeed hLimit
    have hEmptyPages := finalHeap.emptyStore_pages_bound final need spare limit pageLimit
      hFinalPages hReserved hNeed hLimitPages
    have hExpected : expected = { status := 4, dt := lastDt, grid := #[] } := by
      simpa only [Control.retry] using hSame.symm
    change Control.retry fuel.toNat n trials.toNat time dt alpha grid = { status := 4, dt := lastDt, grid := #[] } at hExpected
    let params := resultFrame.params
    let saved := resultFrame.locals.take 71
    have hParams : params.length = 8 := by simp [params, hFrame.params]
    have hSaved : saved.length = 71 := by simp [saved, hFrame.locals]
    have hDtRead : params[4]? = some (.i64 lastDt) := by simp [params, hFrame.params]
    have hDoneRead : saved[5]? = some (.i64 0) := by
      simpa only [saved, List.getElem?_take_of_lt (by decide : 5 < 71), boolWord,
        Bool.false_eq_true, ite_false] using hFrame.done
    obtain ⟨hDoneBound, hDoneValue⟩ := List.getElem_of_getElem? hDoneRead
    have hInput := hLastScratch.frame_eq hFrame.values
    change resultFrame = FixedArraySearch.frame params saved [] 0 0 0 0 0 0 at hInput
    rw [retry_exhausted_shape, hInput]
    wp_run [FixedArraySearch.frame, hParams, hSaved, hDoneRead, hDoneValue, List.length_append,
      List.cons_append, List.nil_append, List.getElem?_append, List.getElem?_cons_zero,
      List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine wp_iff_cons rfl ?_
    simp only [ne_eq, List.take_zero, List.drop_zero, List.nil_append]
    apply retry_failure_program_spec env final finalHeap params saved hParams hSaved
      4 lastDt 0 0 0 0 0 0 hDtRead hStore.heapState hBump hStore.pages _ []
    intro previous current capacity next
    wp_run [retryFailureFrame, FixedArrayResult.finishFrame, FixedArrayFold.resultFrame,
      FixedArraySearch.frame, retryFailureSaved, hParams, hSaved, List.length_append,
      List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
    refine ⟨finalHeap.allocate 8, allocatedNode finalHeap.top 8 finalHeap.nodes, ?_, hResource.1, hEmptyPages,
      ?_, hResource.2.2.1, ?_, hResource.2.2.2⟩
    · simp [hExpected, allocatedNode]
    · simpa only [hExpected] using hResource.2.1
    · simp [hExpected]

theorem retry_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (fuel trials time dt alpha : UInt64)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536) :
    let expected := Control.retry fuel.toNat n trials.toNat time dt alpha grid
    TerminatesWith env module 125 initial
      [.i64 source.root, .i64 source.root, .i64 alpha, .i64 dt, .i64 time,
        .i64 trials, .i64 (UInt64.ofNat n), .i64 fuel]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root, .i64 expected.dt, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧ finalHeap.Owns final result expected.grid ∧
        finalHeap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit ∧
        (expected.status = 0 → normalizedCapacity (UInt64.ofNat grid.size) 7 ≤ result.capacity) ∧
        ∀ (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region) := by
  apply (retry_pages_exact env initial heap source grid n fuel trials time dt alpha spare limit 65536
    hn hIndexed hHeap hOwner hPages (Nat.le_refl _) hReserve hLimit hCap hLimit.le).mono
  rintro final values ⟨finalHeap, result, hValues, hStore, _, hResult⟩
  exact ⟨finalHeap, result, hValues, hStore, hResult⟩

#print axioms retry_pages_exact
#print axioms retry_exact

end Project.EulerReconstructed.Execution
