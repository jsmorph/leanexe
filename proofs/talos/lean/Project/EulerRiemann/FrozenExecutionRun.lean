import Project.EulerRiemann.FrozenRunGuard
import Project.EulerRiemann.FrozenRunResources

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime

macro "run_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [runEntryFrame, func97Def, FixedArrayEqNode.branchPost,
        List.cons_append, List.nil_append, List.append_nil, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Time.endTime,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem run_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (n spare limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800)
    (hHeap : heap.At initial) (hBelow : InitialFreeBelow 1 heap.nodes)
    (hReserve : heap.top.toNat + runBytes n spare ≤ limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hLimitPages : limit ≤ pageLimit * 65536) :
    let expected := Control.run n
    TerminatesWith env module 97 initial [.i64 (UInt64.ofNat n)]
      (fun final values => ∃ finalHeap result,
        values = [.i64 result.root, .i64 result.root, .i64 expected.time, .i64 expected.status] ∧
        RetryStoreAt initial heap final finalHeap ∧
        finalHeap.Owns final result expected.grid ∧ gridCapacity n ≤ result.capacity ∧
        finalHeap.Reserved (gridCapacity n) (spare + 1) limit ∧ final.mem.pages ≤ pageLimit) := by
  let initialLimit := heap.top.toNat + runInitialBytes n
  have hRoom : initialLimit + (spare + 3) * (48 + initialBytes (n * n)) ≤ limit := by
    simpa only [initialLimit, runBytes, Nat.add_assoc] using hReserve
  have hInitialLimit : initialLimit ≤ limit := (Nat.le_add_right _ _).trans hRoom
  have hInit := initial_cells_exact env initial heap n initialLimit pageLimit hn.1 hn.2 hHeap hBelow
    (by simp only [initialLimit, runInitialBytes, Nat.add_assoc, le_refl])
    (hInitialLimit.trans_lt hLimit) (hInitialLimit.trans hCap) hPages hPageLimit
    (hInitialLimit.trans hLimitPages)
  have hFuel : (Time.endTime + 1).toNat = Time.endTime.toNat + 1 := by decide
  refine TerminatesWith.of_wp_entry_for (f := func97Def) rfl ?_ (by decide)
  change wp module func97 _ initial (runEntryFrame n) env
  apply run_guard_spec env initial n hn.1 hn.2
  rw [run_body_shape]
  run_peel
  refine wp_call_tw (endTime_exact env initial) ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  run_peel
  refine wp_call_tw hInit ?_
  rintro current values ⟨currentHeap, source, rfl, hCurrent, hOwner, hCapacity, hTop, hCurrentPages, _⟩
  have hGridCapacity : gridCapacity n ≤ source.capacity := by
    rw [UInt64.le_iff_toNat_le, gridCapacity_toNat n hn.2, hCapacity]
  have hAdvance := advance_pages_exact env current currentHeap source (Traversal.initialCells n)
    n (Time.endTime + 1) 0 spare limit pageLimit hn (Traversal.initialCells_indexed n hn)
    hCurrent.heapState hOwner hGridCapacity hCurrentPages hPageLimit
    (run_advance_reservation currentHeap n spare initialLimit limit hn.2 hTop hRoom)
    hLimit (by rw [hCurrent.cap]; exact hCap) hLimitPages (by rw [hFuel]; simp)
  simp only [hFuel] at hAdvance
  run_peel
  refine wp_call_tw hAdvance ?_
  rintro final values ⟨finalHeap, result, tracked, hValues, hFinal, hFinalPages, hResult, hReserved⟩
  subst values
  run_peel
  refine ⟨finalHeap, result, ?_, hCurrent.trans hFinal, ?_, hResult.capacity, hReserved, True.intro⟩
  · simp [Control.run, hn.1, hn.2, Time.endTime]
  · simpa [Control.run, hn.1, hn.2] using hResult.owner

#print axioms run_exact

end Project.EulerRiemann.Frozen.Execution
