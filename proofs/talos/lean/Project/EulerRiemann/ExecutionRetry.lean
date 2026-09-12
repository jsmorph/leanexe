import Project.EulerRiemann.RetryLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem retry_exact_of_success (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (fuel time dt : UInt64)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (hSuccess : (Control.retry fuel.toNat n time dt grid).status = 0) :
    let expected := Control.retry fuel.toNat n time dt grid
    TerminatesWith env Project.EulerRiemann.«module» 74 initial
      [.i64 source.root, .i64 source.root, .i64 dt, .i64 time, .i64 (UInt64.ofNat n), .i64 fuel]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root, .i64 expected.dt, .i64 0] ∧
        RetryStoreAt initial heap final finalHeap ∧ finalHeap.Owns final result expected.grid ∧
        finalHeap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit ∧
        normalizedCapacity (UInt64.ofNat grid.size) 7 ≤ result.capacity ∧
        ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region) := by
  let expected := Control.retry fuel.toNat n time dt grid
  let entry := func74Def.toLocals [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
    .i64 dt, .i64 source.root, .i64 source.root]
  have hStart : RetryFrameAt entry fuel n time dt source.root 0 0 false := by
    constructor <;> rfl
  have hInv : retryInvariant initial heap n time source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit initial entry :=
    ⟨heap, ⟨hHeap, hPages, rfl, fun _ _ h => h⟩, Or.inl ⟨fuel, dt, hStart, rfl, hReserve⟩⟩
  refine TerminatesWith.of_wp_entry_for (f := func74Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func74 _ initial entry env
  rw [retry_loop_shape, List.append_assoc]
  have hEntryShape : func74.take 4 = [.constI64 0, .localSet 6, .constI64 0, .localSet 11] := rfl
  rw [hEntryShape]
  wp_run [entry, func74Def, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp _ ([.block 0 0 [.loop 0 0 retryLoop]] ++ func74.drop 5) _ initial entry env
  apply retry_loop_spec env initial heap source grid n time expected spare limit initial entry
    hn hIndexed hOwner hSuccess hLimit hCap hInv
  intro final finalHeap resultFrame hStore hDone
  obtain ⟨remaining, acceptedDt, result, hFrame, hResult, hReserved, hCapacity, hSeparated⟩ := hDone
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hFinished := hFrame.done
  have hStatus := hFrame.status
  have hDt := hFrame.outputDt
  have hOwnerRead := hFrame.outputOwner
  have hPointerRead := hFrame.outputPointer
  obtain ⟨hFinishedBound, hFinishedRead⟩ := List.getElem_of_getElem? hFinished
  obtain ⟨hStatusBound, hStatusRead⟩ := List.getElem_of_getElem? hStatus
  obtain ⟨hDtBound, hDtRead⟩ := List.getElem_of_getElem? hDt
  obtain ⟨hOwnerBound, hOwnerValue⟩ := List.getElem_of_getElem? hOwnerRead
  obtain ⟨hPointerBound, hPointerValue⟩ := List.getElem_of_getElem? hPointerRead
  unfold func74
  dsimp only
  retry_guard_peel
  exact ⟨finalHeap, result, ⟨rfl, rfl⟩, hStore, hResult, hReserved, hCapacity, hSeparated⟩

#print axioms retry_exact_of_success

end Project.EulerRiemann.Execution
