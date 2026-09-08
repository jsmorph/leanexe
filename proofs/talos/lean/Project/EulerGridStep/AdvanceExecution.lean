import Project.EulerGridStep.AdvanceReads
import Project.ProofKit.FixedArrayAllocatorWindow

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def advanceCellResult (cell : Project.EulerCellStep.Model.CheckedCell) : List Value :=
  [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
    .i64 cell.momentum, .i64 cell.density, .i64 cell.status]

/-- The existing cell25 theorem computes exactly the clamped-neighbor model. -/
theorem advance_cell_exact {m : Wasm.Module} (layout : Layout m) (env : HostEnv Unit)
    (initial : Store Unit) (ratio : UInt64) (input : Array UInt64) (index : Nat) :
    TerminatesWith env m 25 initial (advanceCellArguments ratio input index)
      (fun final values => final = initial ∧ values = advanceCellResult (Model.cellAt ratio input index)) := by
  have hCall := Project.EulerCellStep.Execution.cellCheckedBits_exact_in_module layout.toCellLayout
    env initial ratio
    (input.getD (previousOffset index) 0) (input.getD (previousOffset index + 1) 0)
    (input.getD (previousOffset index + 2) 0) (input.getD (3 * index) 0)
    (input.getD (3 * index + 1) 0) (input.getD (3 * index + 2) 0)
    (input.getD (nextOffset input.size index) 0) (input.getD (nextOffset input.size index + 1) 0)
    (input.getD (nextOffset input.size index + 2) 0)
  simpa only [advanceCellArguments, advanceCellResult, cellAt_neighbors,
    Project.EulerCellStep.Execution.resultValues] using hCall

theorem advance_function_shape : func35 = advanceOffsets ++ advanceReads ++
    [.call 25] ++ func35.drop 237 := rfl

/-- Full advance35 execution, parameterized by the exact applicable writer34 contract. -/
theorem advanceAt_with_writer {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused output target : UInt64) (input : Array UInt64) (index : Nat)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (P : Store Unit → Prop)
    (hWriter : TerminatesWith env m 34 initial
      (advanceCellResult (Model.cellAt ratio input index) ++
        [.i64 (UInt64.ofNat index), .i64 output, .i64 unused])
      (fun final values => values = [.i64 target, .i64 target] ∧ P final)) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 output, .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 target, .i64 target] ∧ P final) := by
  refine TerminatesWith.of_wp_entry_for (f := func35Def)
    (by simpa [layout.noImports] using layout.advance) ?_ (by simp [layout.noImports])
  change wp m func35 _ initial (advanceEntryFrame ratio inputUnused pointer unused output index) env
  rw [advance_function_shape]
  simp only [List.append_assoc]
  apply advance_offsets_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  apply advance_reads_spec m env initial ratio inputUnused pointer unused output input index hArray hi
  simp only [List.cons_append, List.nil_append]
  refine wp_call_tw (advance_cell_exact layout env initial ratio input index) ?_
  rintro current values ⟨rfl, rfl⟩
  wp_alloc_window_lists [func35, advanceReadFrame, advanceCellArguments,
    advanceEntryFrame, advanceCellResult]
  refine wp_call_tw hWriter ?_
  rintro final values ⟨rfl, hFinal⟩
  wp_alloc_window_lists [func35Def]
  exact hFinal

#print axioms advance_cell_exact
#print axioms advance_function_shape
#print axioms advanceAt_with_writer
end Project.EulerGridStep.Execution
