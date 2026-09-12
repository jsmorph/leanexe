import Project.EulerRiemann.ExecutionInputs
import Project.EulerRiemann.ExecutionCell

namespace Project.EulerRiemann.Execution
open Wasm Project.Euler2DCellStep.Sweep

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def evaluateValues (ratio : UInt64) (input : Inputs) : List Wasm.Value :=
  let out := evaluate ratio input
  [.i64 out.courant, .i64 out.alpha, .i64 out.pressure, .i64 out.energy,
    .i64 out.transverse, .i64 out.momentum, .i64 out.density, .i64 out.status]

theorem evaluate_exact (env : HostEnv Unit) (initial : Store Unit)
    (ratio : UInt64) (input : Inputs) :
    TerminatesWith env Project.EulerRiemann.«module» 62 initial
      (inputsValues input ++ [.i64 ratio])
      (fun final values => final = initial ∧ values = evaluateValues ratio input) := by
  refine TerminatesWith.of_wp_entry_for (f := func62Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func62 _ initial
    (func62Def.toLocals [.i64 ratio,
      .i64 input.left.density, .i64 input.left.mx, .i64 input.left.my, .i64 input.left.energy,
      .i64 input.center.density, .i64 input.center.mx, .i64 input.center.my, .i64 input.center.energy,
      .i64 input.right.density, .i64 input.right.mx, .i64 input.right.my, .i64 input.right.energy]) env
  unfold func62
  wp_run [func62Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (cell_exact env initial ratio
    input.left.density input.left.mx input.left.my input.left.energy
    input.center.density input.center.mx input.center.my input.center.energy
    input.right.density input.right.mx input.right.my input.right.energy) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_run [func62Def, Project.Euler2DCellStep.Execution.resultValues, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  simp [evaluateValues, evaluate, inputsValues, stateValues]

macro "update_cell_peel" : tactic => `(tactic|
  wp_run [func69Def, cellValues, inputsValues, stateValues, evaluateValues,
    List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub])

theorem updateCell_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (axis : Bool) (ratio owner pointer : UInt64)
    (grid : Array Traversal.Cell) (cell : Traversal.Cell)
    (hn : 2 ≤ n ∧ n ≤ 800) (hSize : grid.size = n * n)
    (hi : cell.index < n * n) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerRiemann.«module» 69 initial
      (cellValues cell ++ [.i64 pointer, .i64 owner, .i64 ratio,
        .i64 (boolWord axis), .i64 (UInt64.ofNat n)])
      (fun final values => final = initial ∧
        values = cellValues (Traversal.updateCell n axis ratio grid cell)) := by
  let input := Traversal.cellInputs n axis grid cell
  let out := evaluate ratio input
  refine TerminatesWith.of_wp_entry_for (f := func69Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func69 _ initial
    (func69Def.toLocals [.i64 (UInt64.ofNat n), .i64 (boolWord axis), .i64 ratio,
      .i64 owner, .i64 pointer, .i64 (UInt64.ofNat cell.index), .i64 cell.state.density,
      .i64 cell.state.mx, .i64 cell.state.my, .i64 cell.state.energy,
      .i64 cell.pressure, .i64 cell.status]) env
  unfold func69
  update_cell_peel
  refine wp_call_tw (cellInputs_exact env initial n axis owner pointer grid cell hn hSize hi hGrid) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  update_cell_peel
  refine wp_call_tw (evaluate_exact env initial ratio input) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  update_cell_peel
  refine wp_call_tw (orient_exact env initial axis
    ⟨out.density, out.momentum, out.transverse, out.energy⟩) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  update_cell_peel
  simp [Traversal.updateCell, input, out]

#print axioms evaluate_exact
#print axioms updateCell_exact

end Project.EulerRiemann.Execution
