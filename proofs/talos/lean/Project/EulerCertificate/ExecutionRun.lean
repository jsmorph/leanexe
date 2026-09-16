import Project.EulerCertificate.RunFinish
import Project.EulerCertificate.Solve
import Project.EulerRiemann.RunResources

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option pp.deepTerms false
set_option pp.maxSteps 3000

macro "certificate_run_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [vectorValues, boundsValues, Vectors.zero, runEntryFrame, func189Def, FixedArrayEqNode.branchPost,
        List.cons_append, List.nil_append, List.append_nil, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Time.endTime,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem run_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (n : Nat) (trials : UInt64) (spare limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800)
    (hHeap : heap.At initial) (hBelow : InitialFreeBelow 1 heap.nodes)
    (hReserve : heap.top.toNat + runBytes n spare ≤ limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hLimitPages : limit ≤ pageLimit * 65536) :
    let expected := Solve.run n trials.toNat
    TerminatesWith env module 189 initial [.i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => ∃ finalHeap result,
        values = vectorValues expected.residual ++ [.i64 result.root, .i64 result.root, .i64 expected.time, .i64 expected.status] ∧
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
  refine TerminatesWith.of_wp_entry_for (f := func189Def) rfl ?_ (by decide)
  change wp module func189 _ initial (runEntryFrame n trials) env
  apply run_guard_spec env initial n trials hn.1 hn.2
  unfold runBody func189
  dsimp only
  certificate_run_peel
  refine wp_call_tw hInit ?_
  rintro current values ⟨currentHeap, source, rfl, hCurrent, hOwner, hCapacity, hTop, hCurrentPages, _⟩
  have hGridCapacity : gridCapacity n ≤ source.capacity := by
    rw [UInt64.le_iff_toNat_le, gridCapacity_toNat n hn.2, hCapacity]
  have hAdvance := advance_pages_exact env current currentHeap source (Project.EulerRiemann.Traversal.initialCells n)
    n (Time.endTime + 1) trials 0 Vectors.zero spare limit pageLimit hn (Project.EulerRiemann.Traversal.initialCells_indexed n hn)
    hCurrent.heapState hOwner hGridCapacity hCurrentPages hPageLimit
    (run_advance_reservation currentHeap n spare initialLimit limit hn.2 hTop hRoom)
    hLimit (by
      change limit ≤ current.memoryCap Project.EulerRiemann.«module» 0 * 65536
      rw [hCurrent.cap]
      exact hCap) hLimitPages (by rw [hFuel]; simp)
  simp only [hFuel] at hAdvance
  generalize hRun : Control.advance (Time.endTime.toNat + 1) n trials.toNat 0
    (Project.EulerRiemann.Traversal.initialCells n) Vectors.zero = runResult at hAdvance
  have hInitialTotal := totals_physical_exact env current n source.root source.root
    (Project.EulerRiemann.Traversal.initialCells n) hn.2 hOwner.buffer.values
  generalize hInitialValue : Totals.physical n (Project.EulerRiemann.Traversal.initialCells n) = initialTotal at hInitialTotal
  certificate_run_peel
  refine wp_call_tw hInitialTotal ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  certificate_run_peel
  refine wp_call_tw (endTime_exact env current) ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  certificate_run_peel
  refine wp_call_tw (vector_zero_exact env current) ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  certificate_run_peel
  refine wp_call_tw hAdvance ?_
  rintro final values ⟨finalHeap, result, tracked, hValues, hFinal, hFinalPages, hResult, hReserved⟩
  subst values
  apply run_finish_spec env final _ n trials runResult.status runResult.time result.root runResult.grid
    runResult.boundary initialTotal hn.2 hResult.owner.buffer.values
  · rfl
  · simp only [List.length_set]
    rfl
  · intro i
    fin_cases i <;> simp [vectorValues, boundsValues]
  · rfl
  · intro finalFrame hValues
    have hReport : Solve.run n trials.toNat =
        ⟨runResult.status, runResult.time, runResult.grid,
          Vectors.sub (Vectors.sub (Totals.physical n runResult.grid) initialTotal) runResult.boundary⟩ := by
      simp only [Solve.run, ite_eq_left hn, hRun, hInitialValue]
    refine ⟨finalHeap, result, ?_, hCurrent.trans hFinal, ?_, hResult.capacity, hReserved, hFinalPages⟩
    · simp only [hReport, hValues, vectorValues, boundsValues, List.cons_append, List.nil_append,
        List.take_succ_cons, List.take_zero]
    · simpa only [hReport] using hResult.owner

#print axioms run_exact

end Project.EulerCertificate.Execution
