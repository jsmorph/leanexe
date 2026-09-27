import Project.EulerReconstructed.AdvanceTotalLoop

namespace Project.EulerReconstructed.Execution
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerRiemann.Control (Result)
open Wasm Project.Runtime

theorem advance_pages_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (fuel trials time : UInt64)
    (spare limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hCapacity : gridCapacity n ≤ source.capacity) (hPages : initial.mem.pages ≤ pageLimit)
    (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (gridCapacity n) (spare + 3) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536)
    (hFuel : Time.endTime.toNat - time.toNat < fuel.toNat) :
    let expected := Control.advance fuel.toNat n trials.toNat time grid
    TerminatesWith env module 129 initial
      [.i64 source.root, .i64 source.root, .i64 time, .i64 trials, .i64 (UInt64.ofNat n), .i64 fuel]
      (fun final values => ∃ finalHeap result tracked,
        values = [.i64 result.root, .i64 result.root, .i64 expected.time, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧ final.mem.pages ≤ pageLimit ∧
        AdvanceCurrent initial heap n time expected.time final finalHeap result expected.grid tracked ∧
        finalHeap.Reserved (gridCapacity n) (spare + 1) limit) := by
  let expected := Control.advance fuel.toNat n trials.toNat time grid
  let entry := func129Def.toLocals [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
    .i64 source.root, .i64 source.root]
  have hStart : AdvanceFrameAt entry fuel n trials time source.root 0 0 0 false := by
    constructor <;> rfl
  have hCurrent : AdvanceCurrent initial heap n time time initial heap source grid false :=
    ⟨hIndexed, hOwner, hCapacity, rfl, hOwner⟩
  have hInv : advanceTotalInvariant initial heap n trials time expected spare limit pageLimit initial entry :=
    ⟨heap, ⟨hHeap, hPages.trans hPageLimit, rfl, fun _ _ h => h⟩, hPages,
      Or.inl ⟨fuel, time, source, grid, false, hStart, rfl, hFuel, hCurrent, hReserve⟩⟩
  refine TerminatesWith.of_wp_entry_for (f := func129Def) rfl ?_ (by decide)
  change wp module func129 _ initial entry env
  rw [advance_loop_shape, List.append_assoc]
  have hEntryShape : func129.take 4 = [.constI64 0, .localSet 6, .constI64 0, .localSet 11] := rfl
  rw [hEntryShape]
  wp_run [entry, func129Def, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp _ ([.block 0 0 [.loop 0 0 advanceLoop]] ++ func129.drop 5) _ initial entry env
  apply advance_total_loop_spec env initial heap n trials time expected spare limit pageLimit initial entry
    hn hLimit hCap hPageLimit hLimitPages hInv
  intro final finalHeap resultFrame hStore hFinalPages hDone
  obtain ⟨result, tracked, hFrame, hResult, hReserved⟩ := hDone
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hFinished := hFrame.done
  have hStatus := hFrame.status
  have hOutputTime := hFrame.outputTime
  have hOwnerRead := hFrame.outputOwner
  have hPointerRead := hFrame.outputPointer
  obtain ⟨hFinishedBound, hFinishedRead⟩ := List.getElem_of_getElem? hFrame.done
  obtain ⟨hStatusBound, hStatusRead⟩ := List.getElem_of_getElem? hFrame.status
  obtain ⟨hTimeBound, hTimeRead⟩ := List.getElem_of_getElem? hFrame.outputTime
  obtain ⟨hOwnerBound, hOwnerValue⟩ := List.getElem_of_getElem? hFrame.outputOwner
  obtain ⟨hPointerBound, hPointerValue⟩ := List.getElem_of_getElem? hFrame.outputPointer
  unfold func129
  dsimp only
  reconstructed_retry_guard_peel
  refine ⟨finalHeap, result, ⟨rfl, rfl, rfl⟩, hStore, ?_, hReserved⟩
  cases tracked with
  | false => exact Or.inl hResult
  | true => exact Or.inr hResult

theorem advance_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (fuel trials time : UInt64)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hCapacity : gridCapacity n ≤ source.capacity) (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (gridCapacity n) (spare + 3) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hFuel : Time.endTime.toNat - time.toNat < fuel.toNat) :
    let expected := Control.advance fuel.toNat n trials.toNat time grid
    TerminatesWith env module 129 initial
      [.i64 source.root, .i64 source.root, .i64 time, .i64 trials, .i64 (UInt64.ofNat n), .i64 fuel]
      (fun final values => ∃ finalHeap result tracked,
        values = [.i64 result.root, .i64 result.root, .i64 expected.time, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧
        AdvanceCurrent initial heap n time expected.time final finalHeap result expected.grid tracked ∧
        finalHeap.Reserved (gridCapacity n) (spare + 1) limit) := by
  apply (advance_pages_exact env initial heap source grid n fuel trials time spare limit 65536
    hn hIndexed hHeap hOwner hCapacity hPages (Nat.le_refl _) hReserve hLimit hCap hLimit.le hFuel).mono
  rintro final values ⟨finalHeap, result, tracked, hValues, hStore, _, hResult⟩
  exact ⟨finalHeap, result, tracked, hValues, hStore, hResult⟩

#print axioms advance_pages_exact
#print axioms advance_exact

end Project.EulerReconstructed.Execution
