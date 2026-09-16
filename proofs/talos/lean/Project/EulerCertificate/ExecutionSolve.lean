import Project.EulerCertificate.ExecutionRun
import Project.EulerCertificate.ExecutionPack
import Project.EulerCertificate.SolveSpec

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

def solveBytes (n : Nat) : Nat := runBytes n 0 + packBytes (n * n)

theorem solve_bytes_bound (n : Nat) (hn : n ≤ 800) : solveBytes n ≤ 360483856 := by
  have hRun := run_bytes_bound n hn
  have hSize := Nat.mul_le_mul hn hn
  unfold solveBytes packBytes certificateOutputBytes outputBytes
  omega

macro "certificate_solve_peel" : tactic => `(tactic|
  wp_run [func190, func190Def, vectorValues, boundsValues, List.cons_append, List.nil_append, List.append_nil,
    List.length_set, List.set_cons_zero, List.set_cons_succ,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *])

theorem solve_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (n : Nat) (trials : UInt64) (limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800)
    (hHeap : heap.At initial) (hBelow : InitialFreeBelow 1 heap.nodes)
    (hReserve : heap.top.toNat + solveBytes n ≤ limit)
    (hLimit : limit < 4294967296) (hPages : initial.mem.pages ≤ pageLimit)
    (hPageLimit : pageLimit ≤ 65536) (hLimitPages : limit ≤ pageLimit * 65536)
    (hCap : pageLimit ≤ initial.memoryCap module 0) :
    TerminatesWith env module 190 initial [.i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => ∃ (finalHeap : Heap) (result : FreeNode),
        values = [.i64 result.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final result (Solve.solve n trials.toNat) ∧ final.mem.pages ≤ pageLimit) := by
  let runLimit := heap.top.toNat + runBytes n 0
  have hRoom : runLimit + packBytes (n * n) ≤ limit := by
    simpa only [runLimit, solveBytes, Nat.add_assoc] using hReserve
  have hRunLimit : runLimit ≤ limit := (Nat.le_add_right _ _).trans hRoom
  have hRun := run_exact env initial heap n trials 0 runLimit pageLimit hn hHeap hBelow (by rfl)
    (hRunLimit.trans_lt hLimit)
    ((hRunLimit.trans hLimitPages).trans (Nat.mul_le_mul_right _ hCap))
    hPages hPageLimit (hRunLimit.trans hLimitPages)
  have hGrid := congrArg Project.EulerRiemann.Control.Result.grid (Solve.run_base n trials.toNat)
  have hSize : (Solve.run n trials.toNat).grid.size = n * n := by
    change (Solve.run n trials.toNat).grid = (Project.EulerReconstructed.Control.run n trials.toNat).grid at hGrid
    rw [hGrid]
    exact (Project.EulerReconstructed.Control.run_indexed n trials.toNat hn).1
  refine TerminatesWith.of_wp_entry_for (f := func190Def) rfl ?_ (by decide)
  change wp module func190 _ initial (func190Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials]) env
  certificate_solve_peel
  refine wp_call_tw hRun ?_
  rintro current values ⟨currentHeap, source, rfl, hCurrent, hOwner, _, hReserved, hCurrentPages⟩
  have hTop : currentHeap.top.toNat ≤ runLimit := by
    unfold Heap.Reserved at hReserved
    omega
  have hBudget : OutputBudget current currentHeap (packBytes (Solve.run n trials.toNat).grid.size) pageLimit := by
    rw [hSize]
    refine ⟨by omega, by omega, hCurrentPages, hPageLimit, ?_⟩
    rw [hCurrent.cap]
    exact hCap
  have hOutput := pack_exact env current currentHeap source n pageLimit (Solve.run n trials.toNat)
    hCurrent.heapState hOwner (by rw [hSize]; exact Nat.mul_le_mul hn.2 hn.2) hBudget
  certificate_solve_peel
  refine wp_call_tw hOutput ?_
  rintro final values ⟨finalHeap, result, rfl, hFinalHeap, hResult, hFinalPages⟩
  certificate_solve_peel
  exact ⟨finalHeap, result, rfl, hFinalHeap, hResult, True.intro⟩

#print axioms solve_bytes_bound
#print axioms solve_exact

end Project.EulerCertificate.Execution
