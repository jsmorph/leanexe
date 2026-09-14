import Project.EulerOutwardGrid.Scalar

namespace Project.EulerOutwardGrid.Execution
open Wasm
open Project.EulerRiemann
open Project.EulerRiemann.OutwardMaximum
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.ProofKit.F64Outward (Checked)

theorem cellUpper_exact (env : HostEnv Unit) (initial : Store Unit) (state : State) :
    TerminatesWith env Project.EulerOutwardGrid.«module» 42 initial
      [.i64 state.energy, .i64 state.my, .i64 state.mx, .i64 state.density]
      (fun final values => final = initial ∧ values = checkedValues (cellUpper state)) := by
  refine TerminatesWith.of_wp_entry_for (f := func42Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardGrid.«module» func42 _ initial
    (func42Def.toLocals [.i64 state.density, .i64 state.mx, .i64 state.my, .i64 state.energy]) env
  unfold func42
  wp_run [func42Def]
  outward_call (speed_exact env initial state.density state.mx state.my state.energy)
  outward_call (speed_exact env initial state.density state.my state.mx state.energy)
  outward_call (merge_exact env initial
    (OutwardSpeed.speedUpper state.density state.mx state.my state.energy)
    (OutwardSpeed.speedUpper state.density state.my state.mx state.energy))
  simp [cellUpper, checkedValues]

theorem scanCell_exact (env : HostEnv Unit) (initial : Store Unit)
    (acc : Checked) (cell : Traversal.Cell) :
    TerminatesWith env Project.EulerOutwardGrid.«module» 44 initial
      [.i64 cell.status, .i64 cell.pressure, .i64 cell.state.energy,
        .i64 cell.state.my, .i64 cell.state.mx, .i64 cell.state.density,
        .i64 (UInt64.ofNat cell.index), .i64 acc.value, .i64 acc.status]
      (fun final values => final = initial ∧ values = checkedValues (scanCell acc cell)) := by
  refine TerminatesWith.of_wp_entry_for (f := func44Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardGrid.«module» func44 _ initial
    (func44Def.toLocals [.i64 acc.status, .i64 acc.value, .i64 (UInt64.ofNat cell.index),
      .i64 cell.state.density, .i64 cell.state.mx, .i64 cell.state.my,
      .i64 cell.state.energy, .i64 cell.pressure, .i64 cell.status]) env
  unfold func44
  wp_run [func44Def]
  outward_call (cellUpper_exact env initial cell.state)
  outward_call (merge_exact env initial acc (cellUpper cell.state))
  simp [scanCell, checkedValues]

#print axioms cellUpper_exact
#print axioms scanCell_exact
end Project.EulerOutwardGrid.Execution
