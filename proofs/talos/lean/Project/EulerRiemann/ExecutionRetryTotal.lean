import Project.EulerRiemann.RetryTotalLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity FixedArrayFold

theorem retry_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (fuel time dt : UInt64)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536) :
    let expected := Control.retry fuel.toNat n time dt grid
    TerminatesWith env module 81 initial
      [.i64 source.root, .i64 source.root, .i64 dt, .i64 time, .i64 (UInt64.ofNat n), .i64 fuel]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root, .i64 expected.dt, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧ finalHeap.Owns final result expected.grid ∧
        finalHeap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit ∧
        (expected.status = 0 → normalizedCapacity (UInt64.ofNat grid.size) 7 ≤ result.capacity) ∧
        ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region) := by
  let expected := Control.retry fuel.toNat n time dt grid
  let entry := func81Def.toLocals [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
    .i64 dt, .i64 source.root, .i64 source.root]
  have hStart : RetryFrameAt entry fuel n time dt source.root 0 0 false := by
    constructor <;> rfl
  have hScratch : RetryScratch entry := rfl
  have hInv : retryTotalInvariant initial heap n time source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit initial entry :=
    ⟨heap, ⟨hHeap, hPages, rfl, fun _ _ h => h⟩, Or.inl ⟨⟨fuel, dt, hStart, rfl, hReserve⟩, hScratch⟩⟩
  refine TerminatesWith.of_wp_entry_for (f := func81Def) rfl ?_ (by decide)
  change wp module func81 _ initial entry env
  rw [retry_loop_shape, List.append_assoc]
  have hEntryShape : func81.take 4 = [.constI64 0, .localSet 6, .constI64 0, .localSet 11] := rfl
  rw [hEntryShape]
  wp_run [entry, func81Def, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp _ ([.block 0 0 [.loop 0 0 retryLoop]] ++ func81.drop 5) _ initial entry env
  apply retry_total_loop_spec env initial heap source grid n time expected spare limit initial entry
    hn hIndexed hOwner hLimit hCap hInv
  intro final finalHeap resultFrame hStore hStopped
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
    retry_guard_peel
    exact ⟨finalHeap, result, ⟨rfl, rfl, rfl⟩, hStore, hResult, hReserved, hCapacity, hSeparated⟩
  · let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    have hNeed : (8 : UInt64) ≤ need := by
      rw [UInt64.le_iff_toNat_le]
      exact normalizedCapacity_toNat_ge_eight ..
    have hBound : takeFirstFitFrom 0 8 finalHeap.nodes = none →
        finalHeap.top.toNat + 48 + 8 ≤ limit := hReserved.bump_small_bound (by omega) hNeed
    have hCurrentCap : limit ≤ final.memoryCap module 0 * 65536 := by
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
    have hExpected : expected = { status := 4, dt := lastDt, grid := #[] } := by
      simpa only [Control.retry] using hSame.symm
    change Control.retry fuel.toNat n time dt grid = { status := 4, dt := lastDt, grid := #[] } at hExpected
    let params := resultFrame.params
    let saved := resultFrame.locals.take 45
    have hParams : params.length = 6 := by simp [params, hFrame.params]
    have hSaved : saved.length = 45 := by simp [saved, hFrame.locals]
    have hDtRead : params[3]? = some (.i64 lastDt) := by simp [params, hFrame.params]
    have hDoneRead : saved[5]? = some (.i64 0) := by
      simpa only [saved, List.getElem?_take_of_lt (by decide : 5 < 45), boolWord,
        Bool.false_eq_true, ite_false] using hFrame.done
    obtain ⟨hDoneBound, hDoneValue⟩ := List.getElem_of_getElem? hDoneRead
    have hInput := hLastScratch.frame_eq hFrame.values
    change resultFrame = FixedArraySearch.frame params saved [] 0 0 0 0 0 0 at hInput
    rw [retry_exhausted_shape, hInput]
    wp_run [FixedArraySearch.frame, hParams, hSaved, hDoneRead, hDoneValue, List.length_append,
      List.cons_append, List.nil_append, List.getElem?_append, List.getElem?_cons_zero,
      List.getElem?_cons_succ, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
    refine wp_iff_cons rfl ?_
    simp only [ne_eq, not_false_eq_true, ite_true, List.take_zero, List.drop_zero, List.nil_append]
    apply retry_failure_program_spec env final finalHeap params saved hParams hSaved
      4 lastDt 0 0 0 0 0 0 hDtRead hStore.heapState hBump hStore.pages _ []
    intro previous current capacity next
    wp_run [retryFailureFrame, FixedArrayResult.finishFrame, FixedArrayFold.resultFrame,
      FixedArraySearch.frame, retryFailureSaved, hParams, hSaved, List.length_append,
      List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
    refine ⟨finalHeap.allocate 8, allocatedNode finalHeap.top 8 finalHeap.nodes, ?_, hResource.1,
      ?_, hResource.2.2.1, ?_, hResource.2.2.2⟩
    · simp [hExpected, allocatedNode]
    · simpa only [hExpected] using hResource.2.1
    · simp [hExpected]

#print axioms retry_exact

end Project.EulerRiemann.Execution
