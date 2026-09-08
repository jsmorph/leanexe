import Project.EulerGridStep.AdvanceExecution
import Project.EulerGridStep.WriterRejected
import Project.EulerGridStep.FreshWriterRejected

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Both allocation choices implement the same rejected-writer result contract. -/
theorem writeCell_rejected_choice {m : Wasm.Module} (layout : Layout m)
    (choice : FieldAllocation) (env : HostEnv Unit) (initial : Store Unit)
    (unused source : UInt64) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (hRejected : cell.status ≠ 0)
    (hOutput : UInt64Array.At initial source output) (hNonempty : 0 < output.size)
    (hValid : choice.Valid initial source output) (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env m 34 initial
      (advanceCellResult cell ++ [.i64 (UInt64.ofNat index), .i64 source, .i64 unused])
      (fun final values => values = [.i64 choice.root, .i64 choice.root] ∧
        FieldResult choice initial final source output 0 1) := by
  cases choice with
  | fresh heapTop allocs =>
      exact writeCell_fresh_rejected_exact_in_module layout env initial unused source heapTop allocs
        output index cell hRejected hOutput hNonempty hValid hPages
  | reuse root capacity next allocs =>
      exact writeCell_rejected_exact_in_module layout env initial unused source root capacity next allocs
        output index cell hRejected hOutput hNonempty hValid

/-- Full rejected advance for either allocation path, including exact status output and old-grid preservation. -/
theorem advanceAt_rejected {m : Wasm.Module} (layout : Layout m)
    (choice : FieldAllocation) (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused source : UInt64) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hRejected : (Model.cellAt ratio input index).status ≠ 0)
    (hOutput : UInt64Array.At initial source output) (hNonempty : 0 < output.size)
    (hValid : choice.Valid initial source output) (hPages : initial.mem.pages ≤ 65536)
    (hSeparate : ObjectsSeparate choice.root output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 source, .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 choice.root, .i64 choice.root] ∧
        UInt64Array.At final choice.root (Model.advanceAt ratio input output index) ∧
        FieldResult choice initial final source output 0 1 ∧ UInt64Array.At final pointer input) := by
  apply advanceAt_with_writer layout env initial ratio inputUnused pointer unused source choice.root
    input index hInput hi
  apply (writeCell_rejected_choice layout choice env initial unused source output index
    (Model.cellAt ratio input index) hRejected hOutput hNonempty hValid hPages).mono
  rintro final values ⟨hValues, hResult⟩
  refine ⟨hValues, ?_, hResult, hResult.preserves_array pointer input hInput hSeparate⟩
  simpa [Model.advanceAt, hRejected] using hResult.write.outputAt

#print axioms writeCell_rejected_choice
#print axioms advanceAt_rejected
end Project.EulerGridStep.Execution
