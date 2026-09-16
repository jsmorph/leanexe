import Project.EulerCertificate.VectorExecution
import Project.EulerCertificate.Totals
import Project.EulerRiemann.ExecutionInputs

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.EulerRiemann.Traversal (Cell)
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)
open Project.EulerRiemann.Execution (cellValues stateValues)

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

theorem totals_addCell_exact (env : HostEnv Unit) (initial : Store Unit)
    (acc : Vector) (cell : Cell) :
    TerminatesWith env Project.EulerCertificate.«module» 73 initial
      (cellValues cell ++ vectorValues acc)
      (fun final values => final = initial ∧ values = vectorValues (Totals.addCell acc cell)) := by
  have stateCall := vector_state_exact env initial cell.state
  generalize hs : Vectors.state cell.state = state at stateCall
  have addCall := vector_add_exact env initial acc state
  generalize ha : Vectors.add acc state = out at addCall
  simp only [Totals.addCell, hs, ha]
  refine TerminatesWith.of_wp_entry_for (f := func73Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func73 _ initial
    (func73Def.toLocals [.i64 acc.mass.status, .i64 acc.mass.lower, .i64 acc.mass.upper, .i64 acc.momentum.status, .i64 acc.momentum.lower, .i64 acc.momentum.upper, .i64 acc.transverse.status, .i64 acc.transverse.lower, .i64 acc.transverse.upper, .i64 acc.energy.status, .i64 acc.energy.lower, .i64 acc.energy.upper, .i64 (UInt64.ofNat cell.index),
      .i64 cell.state.density, .i64 cell.state.mx, .i64 cell.state.my,
      .i64 cell.state.energy, .i64 cell.pressure, .i64 cell.status]) env
  unfold func73
  wp_run [func73Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  guard_call stateCall
  guard_call addCall
  simp [vectorValues, boundsValues, cellValues]

#print axioms totals_addCell_exact
end Project.EulerCertificate.Execution
