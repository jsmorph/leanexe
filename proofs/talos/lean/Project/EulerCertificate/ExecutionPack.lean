import Project.EulerCertificate.OutputBase
import Project.EulerCertificate.OutputCompose
import Project.EulerCertificateFlux.Physical

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit
open Project.EulerRiemann Project.EulerRiemann.Execution
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

def packBytes (size : Nat) : Nat := outputBytes size + certificateOutputBytes (4 + 2 * size)

def packEntryFrame (n : Nat) (report : Solve.Report) (root : UInt64) : Locals :=
  func15Def.toLocals [.i64 (UInt64.ofNat n), .i64 report.status, .i64 report.time, .i64 root, .i64 root,
    .i64 report.residual.mass.status, .i64 report.residual.mass.lower, .i64 report.residual.mass.upper,
    .i64 report.residual.momentum.status, .i64 report.residual.momentum.lower, .i64 report.residual.momentum.upper,
    .i64 report.residual.transverse.status, .i64 report.residual.transverse.lower, .i64 report.residual.transverse.upper,
    .i64 report.residual.energy.status, .i64 report.residual.energy.lower, .i64 report.residual.energy.upper]

def packStart : Wasm.Program := func15.take 16

def packPrepare : Wasm.Program := (func15.drop 16).take 30

theorem pack_shape : func15 = packStart ++ packPrepare ++ func15.drop 46 := rfl

theorem pack_start_shape : packStart =
  [.localGet 0, .localSet 17, .localGet 2, .localSet 18, .localGet 1, .localSet 19,
    .localGet 3, .localSet 20, .localGet 4, .localSet 21,
    .localGet 17, .localGet 18, .localGet 19, .localGet 20, .localGet 21, .call 3] := rfl

theorem pack_prepare_shape : packPrepare =
  [.localSet 23, .localSet 22, .localGet 22, .localSet 24, .localGet 23, .localSet 25] ++
    (List.range 12).flatMap (fun i => [.localGet (5 + i), .localSet (26 + i)]) := rfl

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option pp.deepTerms false
set_option pp.maxSteps 3000

macro "certificate_pack_peel" : tactic => `(tactic|
  wp_run [packEntryFrame, func15Def, vectorValues, boundsValues, List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff])

theorem pack_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (source : FreeNode)
    (n pageLimit : Nat) (report : Solve.Report)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source report.grid) (hSize : report.grid.size ≤ 640000)
    (hBudget : OutputBudget initial heap (packBytes report.grid.size) pageLimit) :
    TerminatesWith env module 15 initial
      (vectorValues report.residual ++
        [.i64 source.root, .i64 source.root, .i64 report.time, .i64 report.status, .i64 (UInt64.ofNat n)])
      (fun final values => ∃ (finalHeap : Heap) (result : FreeNode),
        values = [.i64 result.root, .i64 result.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final result (Solve.pack n report) ∧ final.mem.pages ≤ pageLimit) := by
  have hOutput := output_budget_exact env initial heap source report.grid n
    (certificateOutputBytes (Output.pack n report.time report.status report.grid).size) pageLimit
    report.time report.status hHeap hOwner hSize (by simpa only [Output.pack_size, packBytes] using hBudget)
  refine TerminatesWith.of_wp_entry_for (f := func15Def) rfl ?_ (by decide)
  change wp module func15 _ initial (packEntryFrame n report source.root) env
  rw [pack_shape, List.append_assoc, pack_start_shape]
  certificate_pack_peel
  refine wp_call_tw hOutput ?_
  rintro current values ⟨currentHeap, base, rfl, hCurrentHeap, hBase, hCurrentBudget⟩
  rw [pack_prepare_shape]
  certificate_pack_peel
  apply output_compose_spec env current currentHeap _ base
    (Output.pack n report.time report.status report.grid) report.residual pageLimit
  · rfl
  · simp only [List.length_set]
    rfl
  · rfl
  · intro index hFirst hLast
    interval_cases index <;> refine ⟨0, ?_⟩ <;> simp [Locals.get]
  · simp [Locals.get]
  · simp [Locals.get]
  · intro i
    fin_cases i <;> simp [Locals.get, Solve.certificateWords]
  · exact hCurrentHeap
  · exact hBase
  · rw [Output.pack_size]
    omega
  · exact hCurrentBudget
  · intro final finalHeap result resultFrame hFinalHeap hFinalOwner hFinalBudget hValues
    refine ⟨finalHeap, result, ?_, hFinalHeap, ?_, hFinalBudget.pages⟩
    · rw [hValues]
      rfl
    · simpa only [Solve.pack, outputCertificateWords, Solve.certificateWords] using hFinalOwner

#print axioms pack_shape
#print axioms pack_start_shape
#print axioms pack_prepare_shape
#print axioms pack_exact
end Project.EulerCertificate.Execution
