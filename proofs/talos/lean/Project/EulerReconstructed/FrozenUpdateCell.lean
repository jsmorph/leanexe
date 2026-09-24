import Project.EulerReconstructed.FrozenCellStencil
import Project.EulerReconstructed.FrozenReconstructedStep

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.Euler2DCellStep.Sweep
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Traversal (Cell)
open Project.EulerRiemann.Frozen.Execution (cellValues stateValues boolWord)
open Project.EulerRiemann.Frozen.OutwardNumerics (reconstructedStepCheckedBits)

set_option maxRecDepth 32768

macro "reconstructed_update_peel" : tactic => `(tactic|
  wp_run [func120Def, cellValues, stencilValues, stateValues,
    Project.EulerOutwardFaceStep.Execution.cellValues,
    Project.EulerReconstruction.Execution.stateValues,
    List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub])

set_option maxHeartbeats 1000000 in
theorem updateCell_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (fuel : UInt64) (axis : Bool) (ratio owner pointer : UInt64)
    (grid : Array Cell) (cell : Cell)
    (hn : 2 ≤ n ∧ n ≤ 800) (hSize : grid.size = n * n)
    (hi : cell.index < n * n) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 120 initial
      (cellValues cell ++ [.i64 pointer, .i64 owner, .i64 ratio,
        .i64 (boolWord axis), .i64 fuel, .i64 (UInt64.ofNat n)])
      (fun final values => final = initial ∧
        values = cellValues (Traversal.updateCell n fuel.toNat axis ratio grid cell)) := by
  let input := Traversal.cellStencil n axis grid cell
  let out := reconstructedStepCheckedBits fuel.toNat ratio
    input.farLeft input.left input.center input.right input.farRight
  unfold cellValues
  refine TerminatesWith.of_wp_entry_for (f := func120Def) rfl ?_ (by decide)
  change wp Project.EulerReconstructed.Frozen.«module» func120 _ initial
    (func120Def.toLocals [.i64 (UInt64.ofNat n), .i64 fuel, .i64 (boolWord axis), .i64 ratio,
      .i64 owner, .i64 pointer, .i64 (UInt64.ofNat cell.index), .i64 cell.state.density,
      .i64 cell.state.mx, .i64 cell.state.my, .i64 cell.state.energy,
      .i64 cell.pressure, .i64 cell.status]) env
  unfold func120
  reconstructed_update_peel
  refine wp_call_tw (cellStencil_exact env initial n axis owner pointer grid cell hn hSize hi hGrid) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  reconstructed_update_peel
  refine wp_call_tw (reconstructed_step_exact env initial fuel ratio
    input.farLeft input.left input.center input.right input.farRight) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  reconstructed_update_peel
  refine wp_call_tw (orient_exact env initial axis
    ⟨out.density, out.momentum, out.transverse, out.energy⟩) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  reconstructed_update_peel
  simp [Traversal.updateCell, input, out]

#print axioms updateCell_exact
end Project.EulerReconstructed.Frozen.Execution
