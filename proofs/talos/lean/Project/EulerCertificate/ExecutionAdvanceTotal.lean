import Project.EulerCertificate.AdvanceTotalLoop
import Project.EulerCertificate.AdvanceReturn

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerCertificate.Control (Result)
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)
open Wasm Project.Runtime

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

theorem advance_pages_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (fuel trials time : UInt64) (boundary : Vector)
    (spare limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hCapacity : gridCapacity n ≤ source.capacity) (hPages : initial.mem.pages ≤ pageLimit)
    (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (gridCapacity n) (spare + 3) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536)
    (hFuel : Time.endTime.toNat - time.toNat < fuel.toNat) :
    let expected := Control.advance fuel.toNat n trials.toNat time grid boundary
    TerminatesWith env module 184 initial
      (vectorValues boundary ++ [.i64 source.root, .i64 source.root, .i64 time, .i64 trials, .i64 (UInt64.ofNat n), .i64 fuel])
      (fun final values => ∃ finalHeap result tracked,
        values = vectorValues expected.boundary ++ [.i64 result.root, .i64 result.root, .i64 expected.time, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧ final.mem.pages ≤ pageLimit ∧
        AdvanceCurrent initial heap n time expected.time final finalHeap result expected.grid tracked ∧
        finalHeap.Reserved (gridCapacity n) (spare + 1) limit) := by
  let expected := Control.advance fuel.toNat n trials.toNat time grid boundary
  let entry := func184Def.toLocals (advanceParams fuel n trials time source.root boundary)
  have hStart : AdvanceFrameAt entry fuel n trials time source.root 0 0 0 false boundary := by
    constructor <;> rfl
  have hCurrent : AdvanceCurrent initial heap n time time initial heap source grid false :=
    ⟨hIndexed, hOwner, hCapacity, rfl, hOwner⟩
  have hInv : advanceTotalInvariant initial heap n trials time expected spare limit pageLimit initial entry :=
    ⟨heap, ⟨hHeap, hPages.trans hPageLimit, rfl, fun _ _ h => h⟩, hPages,
      Or.inl ⟨fuel, time, source, grid, boundary, false, hStart, rfl, hFuel, hCurrent, hReserve⟩⟩
  refine TerminatesWith.of_wp_entry_for (f := func184Def) rfl ?_ (by decide)
  change wp module func184 _ initial entry env
  rw [advance_loop_shape, List.append_assoc]
  have hEntryShape : func184.take 4 = [.constI64 0, .localSet 18, .constI64 0, .localSet 35] := rfl
  rw [hEntryShape]
  wp_run [entry, func184Def, advanceParams, vectorValues, boundsValues, List.set, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  change wp _ ([.block 0 0 [.loop 0 0 advanceLoop]] ++ func184.drop 5) _ initial entry env
  apply advance_total_loop_spec env initial heap n trials time expected spare limit pageLimit initial entry
    hn hLimit hCap hPageLimit hLimitPages hInv
  intro final finalHeap resultFrame hStore hFinalPages hDone
  obtain ⟨result, tracked, hFrame, hResult, hReserved⟩ := hDone
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hFinished := hFrame.done
  obtain ⟨hFinishedBound, hFinishedRead⟩ := List.getElem_of_getElem? hFrame.done
  rw [advance_return_shape]
  unfold func184
  dsimp only
  certificate_advance_guard_peel
  have hCleared : ({ resultFrame with values := [] } : Locals) = resultFrame :=
    Project.ProofKit.Frame.ext _ _ rfl rfl hValues.symm
  rw [hCleared]
  apply advance_return_spec env final resultFrame expected.status expected.time result.root expected.boundary hFrame
  refine ⟨finalHeap, result, rfl, hStore, hFinalPages, ?_, hReserved⟩
  cases tracked with
  | false => exact Or.inl hResult
  | true => exact Or.inr hResult

theorem advance_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (fuel trials time : UInt64) (boundary : Vector)
    (spare limit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hCapacity : gridCapacity n ≤ source.capacity) (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (gridCapacity n) (spare + 3) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hFuel : Time.endTime.toNat - time.toNat < fuel.toNat) :
    let expected := Control.advance fuel.toNat n trials.toNat time grid boundary
    TerminatesWith env module 184 initial
      (vectorValues boundary ++ [.i64 source.root, .i64 source.root, .i64 time, .i64 trials, .i64 (UInt64.ofNat n), .i64 fuel])
      (fun final values => ∃ finalHeap result tracked,
        values = vectorValues expected.boundary ++ [.i64 result.root, .i64 result.root, .i64 expected.time, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧
        AdvanceCurrent initial heap n time expected.time final finalHeap result expected.grid tracked ∧
        finalHeap.Reserved (gridCapacity n) (spare + 1) limit) := by
  apply (advance_pages_exact env initial heap source grid n fuel trials time boundary spare limit 65536
    hn hIndexed hHeap hOwner hCapacity hPages (Nat.le_refl _) hReserve hLimit hCap hLimit.le hFuel).mono
  rintro final values ⟨finalHeap, result, tracked, hValues, hStore, _, hResult⟩
  exact ⟨finalHeap, result, tracked, hValues, hStore, hResult⟩

#print axioms advance_pages_exact
#print axioms advance_exact

end Project.EulerCertificate.Execution
