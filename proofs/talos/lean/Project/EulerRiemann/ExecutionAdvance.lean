import Project.EulerRiemann.AdvanceLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem advance_exact_of_success (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (fuel time : UInt64)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hCapacity : gridCapacity n ≤ source.capacity)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (gridCapacity n) (spare + 3) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (hFuel : Time.endTime.toNat - time.toNat < fuel.toNat)
    (hSuccess : (Control.advance fuel.toNat n time grid).status = 0) :
    let expected := Control.advance fuel.toNat n time grid
    TerminatesWith env Project.EulerRiemann.«module» 78 initial
      [.i64 source.root, .i64 source.root, .i64 time, .i64 (UInt64.ofNat n), .i64 fuel]
      (fun final values => ∃ finalHeap result tracked,
        values = [.i64 result.root, .i64 result.root, .i64 expected.time, .i64 0] ∧
        RetryStoreAt initial heap final finalHeap ∧ expected.time = Time.endTime ∧
        AdvanceCurrent initial heap n time expected.time final finalHeap result expected.grid tracked ∧
        finalHeap.Reserved (gridCapacity n) (spare + 2) limit) := by
  let expected := Control.advance fuel.toNat n time grid
  let entry := func78Def.toLocals [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
    .i64 source.root, .i64 source.root]
  have hStart : AdvanceFrameAt entry fuel n time source.root 0 0 0 false := by
    constructor <;> rfl
  have hCurrent : AdvanceCurrent initial heap n time time initial heap source grid false :=
    ⟨hIndexed, hOwner, hCapacity, rfl, hOwner⟩
  have hInv : advanceInvariant initial heap n time expected spare limit initial entry :=
    ⟨heap, ⟨hHeap, hPages, rfl, fun _ _ h => h⟩,
      Or.inl ⟨fuel, time, source, grid, false, hStart, rfl, hFuel, hCurrent, hReserve⟩⟩
  refine TerminatesWith.of_wp_entry_for (f := func78Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func78 _ initial entry env
  rw [advance_loop_shape, List.append_assoc]
  have hEntryShape : func78.take 4 = [.constI64 0, .localSet 5, .constI64 0, .localSet 10] := rfl
  rw [hEntryShape]
  wp_run [entry, func78Def, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp _ ([.block 0 0 [.loop 0 0 advanceLoop]] ++ func78.drop 5) _ initial entry env
  apply advance_loop_spec env initial heap n time expected spare limit initial entry
    hn hSuccess hLimit hCap hInv
  intro final finalHeap resultFrame hStore hDone
  obtain ⟨remaining, result, tracked, hFrame, hTime, hResult, hReserved⟩ := hDone
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hFinished := hFrame.done
  have hStatus := hFrame.status
  have hOutputTime := hFrame.outputTime
  have hOwner := hFrame.outputOwner
  have hPointer := hFrame.outputPointer
  obtain ⟨hFinishedBound, hFinishedRead⟩ := List.getElem_of_getElem? hFrame.done
  obtain ⟨hStatusBound, hStatusRead⟩ := List.getElem_of_getElem? hFrame.status
  obtain ⟨hTimeBound, hTimeRead⟩ := List.getElem_of_getElem? hFrame.outputTime
  obtain ⟨hOwnerBound, hOwnerRead⟩ := List.getElem_of_getElem? hFrame.outputOwner
  obtain ⟨hPointerBound, hPointerRead⟩ := List.getElem_of_getElem? hFrame.outputPointer
  unfold func78
  dsimp only
  retry_guard_peel
  refine ⟨finalHeap, result, ⟨rfl, hTime.symm⟩, hStore, hTime, ?_, hReserved⟩
  cases tracked with
  | false => exact Or.inl hResult
  | true => exact Or.inr hResult

#print axioms advance_exact_of_success

end Project.EulerRiemann.Execution
